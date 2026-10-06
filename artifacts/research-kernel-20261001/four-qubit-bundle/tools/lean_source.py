"""Small lexical utilities shared by certification tooling (not a Lean parser)."""
import re

MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def code_only(source):
    """Blank nested comments and strings, preserving offsets and line numbers."""
    out = list(source)
    index, depth = 0, 0
    while index < len(source):
        if depth:
            if source.startswith('/-', index):
                out[index:index + 2] = '  '
                depth += 1
                index += 2
            elif source.startswith('-/', index):
                out[index:index + 2] = '  '
                depth -= 1
                index += 2
            else:
                if source[index] != '\n':
                    out[index] = ' '
                index += 1
        elif source.startswith('/-', index):
            out[index:index + 2] = '  '
            depth, index = 1, index + 2
        elif source.startswith('--', index):
            end = source.find('\n', index)
            end = len(source) if end < 0 else end
            out[index:end] = ' ' * (end - index)
            index = end
        elif source[index] == '"':
            out[index] = ' '
            index += 1
            while index < len(source):
                char = source[index]
                if char != '\n':
                    out[index] = ' '
                index += 1
                if char == '\\' and index < len(source):
                    if source[index] != '\n':
                        out[index] = ' '
                    index += 1
                elif char == '"':
                    break
        else:
            index += 1
    if depth:
        raise ValueError('unterminated Lean block comment')
    return ''.join(out)


def imports(source):
    result = []
    for match in re.finditer(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',
                             code_only(source), re.M):
        for name in match.group(1).split():
            if not MODULE_NAME.fullmatch(name):
                raise ValueError('unsupported import syntax: ' + name)
            if name not in result:
                result.append(name)
    return result


def audit_names(source):
    result = []
    for match in re.finditer(r'^\s*#print\s+axioms\s+([^\n]+)', code_only(source), re.M):
        name = match.group(1).strip()
        if not MODULE_NAME.fullmatch(name):
            raise ValueError('unsupported axiom audit name: ' + name)
        result.append(name)
    return result
