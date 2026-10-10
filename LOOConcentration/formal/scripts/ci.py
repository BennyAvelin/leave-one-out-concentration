#!/usr/bin/env python3
"""Verify the complete revised-manuscript release without building dependencies."""
from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, tempfile, time
from source_scan import code_only
P=Path(__file__).resolve().parents[1]
OUT=P/'verification'
ROOTS=['LOOConcentrationRevision','LOOConcentrationManuscript',
       'LOOConcentrationManuscript.Supplementary','LOOConcentrationManuscript.ModelSelection']
PROJECT_PREFIXES=('LOOConcentration.','LOOConcentrationRevision.','LOOConcentrationManuscript.')
FORBIDDEN=r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe|maxHeartbeats|maxRecDepth)\b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def validate_sources(project=P):
    manifest=json.loads((project/'PUBLIC_SOURCES.json').read_text())
    sources=manifest['sources']
    for rel,h in sources.items():
        path=Path(rel)
        if path.is_absolute() or '..' in path.parts:raise ValueError('Invalid public input path')
        f=project/path
        if not f.is_file() or f.is_symlink() or sha(f)!=h:raise ValueError('Public source drift: '+rel)
    all_lean={rel for rel in sources if rel.endswith('.lean')}
    production={rel for rel in all_lean if not rel.startswith('challenges/')}
    actual={str(f.relative_to(project)) for f in project.rglob('*.lean')
            if '.lake' not in f.relative_to(project).parts and 'verification' not in f.relative_to(project).parts}
    if actual!=all_lean:raise ValueError('Unregistered or missing Lean source')
    modules={rel.removesuffix('.lean').replace('/','.') for rel in production}
    if modules!=set(manifest['production_modules']):raise ValueError('Module allowlist drift')
    imports={}
    for module in modules:
        if not re.fullmatch(r'[A-Za-z]\w*(?:\.[A-Za-z]\w*)*',module):raise ValueError('Invalid module path')
        code=code_only((project/(module.replace('.','/')+'.lean')).read_text())
        token=re.search(FORBIDDEN,code)
        if token:raise ValueError('Forbidden production token: '+module+': '+token.group(0))
        check_code=code
        # These two inherited, scoped style-linter exceptions do not disable kernel checking.
        if module in {'LOOConcentration.FunctionalInequalities.WeightedLogSum',
                      'LOOConcentrationManuscript.Internal.RidgeVarianceCoordinateDerivative'}:
            check_code=re.sub(r'set_option\s+linter\.style\.haveILetI\s+false\s+in', '', check_code)
        if re.search(r'set_option\s+(?:linter[^\s]*\s+false|debug\.skipKernelTC\s+true|kernel\.check\s+false)',check_code):
            raise ValueError('Check override requires review: '+module)
        imports[module]=re.findall(r'^import ([\w.]+)$',code,re.M)
    seen=set();todo=ROOTS[:]
    while todo:
        module=todo.pop()
        if module in seen:continue
        if module not in modules:
            if (project/(module.replace('.', '/')+'.lean')).is_file():raise ValueError('Production imports a nonproduction module: '+module)
            if module.startswith(PROJECT_PREFIXES) or module in ROOTS:raise ValueError('Missing project import: '+module)
            continue
        seen.add(module);todo.extend(imports[module])
    if seen!=modules:raise ValueError('Source outside the requested import closure')
    if manifest['entry_points']!=ROOTS:raise ValueError('Entry-point drift')
    return sources,sorted(modules)

def dependency_guard():
    records=[]
    for row in json.loads((P/'lake-manifest.json').read_text())['packages']:
        if row['type']!='git':raise ValueError('Non-Git dependency')
        pkg=P/'.lake/packages'/row['name']
        head=subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD'],text=True).strip()
        dirty=subprocess.check_output(['git','-C',str(pkg),'status','--porcelain'],text=True).strip()
        if head!=row['rev'] or dirty:raise ValueError('Dependency is not clean at pin: '+row['name'])
        records.append({'package':row['name'],'revision':head})
    mathlib=P/'.lake/packages/mathlib/.lake/build/lib'
    if sum(1 for _ in mathlib.rglob('*.olean'))<7000:raise ValueError('Fetch pinned Mathlib caches first')
    return records

def execute(name,command,records,own_build=False):
    start=time.monotonic();log=OUT/(name+'.log');unexpected=None
    print('RUN:',name,flush=True)
    with log.open('w') as output:
        process=subprocess.Popen(command,cwd=P,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                                 text=True,bufsize=1,start_new_session=True)
        try:
            for line in process.stdout:
                output.write(line);output.flush();print(line,end='',flush=True)
                if own_build:
                    match=re.search(r'\b(?:Built|Building) ([A-Z][\w.]*)\b',line)
                    if match and not (P/(match.group(1).replace('.','/')+'.lean')).is_file():
                        unexpected=match.group(1);os.killpg(process.pid,signal.SIGTERM);break
            code=process.wait()
        except BaseException:
            if process.poll() is None:os.killpg(process.pid,signal.SIGTERM)
            process.wait();raise
    records.append({'stage':name,'command':command,'exit_code':code,
                    'elapsed_seconds':time.monotonic()-start,'log':str(log.relative_to(P))})
    if unexpected:raise ValueError('Upstream compilation observed: '+unexpected)
    if code:raise ValueError(name+' failed with exit '+str(code))

def main():
    OUT.mkdir(exist_ok=True);result={'verdict':'FAIL','checks':[]}
    try:
        sources,modules=validate_sources();before=dependency_guard()
        result['production_module_count']=len(modules);result['production_modules']=modules
        result['source_sha256']=sources;result['dependencies']=before
        result['lean_toolchain']=(P/'lean-toolchain').read_text().strip()
        execute('production-build',['lake','--no-ansi','--no-cache','build',*modules],result['checks'],True)
        execute('dependency-anchors',[sys.executable,'scripts/check_dependency_anchors.py'],result['checks'])
        manifest=json.loads((P/'revision-anchors.json').read_text())
        for a in manifest['anchors']:
            if sha(P/a['path'])!=a['sha256']:raise ValueError('Anchor drift: '+a['export'])
        exports=sorted(set([a['export'] for a in manifest['anchors']]+manifest['correspondence_axiom_exports']))
        with tempfile.TemporaryDirectory(prefix='loo-revision-axioms-') as directory:
            probe=Path(directory)/'Audit.lean'
            probe.write_text(''.join('import '+m+'\n' for m in modules)+''.join('#print axioms '+n+'\n' for n in exports))
            execute('axioms',['lake','env','lean',str(probe)],result['checks'])
        axes=re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",(OUT/'axioms.log').read_text(),re.S)
        if len(axes)!=len(exports) or {n for n,a in axes}!=set(exports):raise ValueError('Incomplete axiom audit')
        for n,a in axes:
            if not set(x.strip() for x in a.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'}:
                raise ValueError('Forbidden axiom: '+n)
        if before!=dependency_guard():raise ValueError('Dependency pins changed during validation')
        if sources!=validate_sources()[0]:raise ValueError('Public inputs changed during validation')
        execute('challenge-generator',[sys.executable,'challenges/generate.py'],result['checks'])
        execute('challenge-comparator',[sys.executable,'challenges/compare.py'],result['checks'])
        execute('challenge-regressions',[sys.executable,'challenges/test_comparator.py'],result['checks'])
        for report in ['latest','regressions']:
            if json.loads((P/'challenges/reports'/report/'result.json').read_text())['verdict']!='PASS':
                raise ValueError('Challenge checker did not pass: '+report)
        if sources!=validate_sources()[0] or before!=dependency_guard():raise ValueError('Inputs changed during challenge checks')
        result.update(verdict='PASS',axiom_exports_checked=len(axes),production_holes=0,authorized_holes=4)
        print('PASS:',len(modules),'production modules;',len(axes),'standard-only axiom exports',flush=True)
    except (ValueError,OSError,subprocess.CalledProcessError) as error:
        result['reason']=str(error);print('FAIL:',error,file=sys.stderr)
    (OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    return 0 if result['verdict']=='PASS' else 1
if __name__=='__main__':sys.exit(main())
