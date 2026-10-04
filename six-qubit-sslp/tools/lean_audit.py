"""Parse axiom-audit roots without changing the content-validated build lexer."""
import re

from lean_source import MODULE_NAME, code_only


def audit_names(source):
    code = code_only(source)
    result = []
    for match in re.finditer(r'^\s*#print\s+axioms\s+([^\n]+)', code, re.M):
        name = match.group(1).strip()
        if not MODULE_NAME.fullmatch(name):
            raise ValueError('unsupported axiom audit name: ' + name)
        result.append(name)
    for match in re.finditer(r'^\s*#certification_axioms\s*\[([^\]]*)\]', code, re.M):
        for value in match.group(1).split(','):
            name = value.strip()
            if not MODULE_NAME.fullmatch(name):
                raise ValueError('unsupported axiom audit name: ' + name)
            result.append(name)
    return result
