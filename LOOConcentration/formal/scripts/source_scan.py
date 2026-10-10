"""Blank Lean comments/strings before scanning production tokens."""

class Rejected(ValueError):
    pass

def code_only(text):
    """Blank nested comments and strings while preserving line/column layout."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        c = text[i]
        if line:
            if c == '\n':
                line = False
            else:
                out[i] = ' '
            i += 1
        elif depth:
            if text.startswith('/-', i):
                out[i:i+2] = [' ', ' ']; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = [' ', ' ']; depth -= 1; i += 2
            else:
                if c != '\n': out[i] = ' '
                i += 1
        elif string:
            if c == '\\' and i + 1 < len(text):
                out[i:i+2] = [' ', '\n' if text[i+1] == '\n' else ' ']; i += 2
            else:
                if c != '\n': out[i] = ' '
                if c == '"': string = False
                i += 1
        elif text.startswith('--', i):
            out[i:i+2] = [' ', ' ']; line = True; i += 2
        elif text.startswith('/-', i):
            out[i:i+2] = [' ', ' ']; depth = 1; i += 2
        elif c == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise Rejected('Unterminated source comment/string')
    return ''.join(out)

