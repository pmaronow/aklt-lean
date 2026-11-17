"""Reversible visibility-only envelope for generated H1 modules.

The arithmetic text is preserved byte for byte. Unwrapping before bundling
keeps the historical owner map independent of the visibility header.
"""
import re

PREFIX = 'module\n\n'
SECTION = '\n@[expose] public section\nset_option backward.proofsInPublic true\n'


def unwrap(text):
    if not text.startswith(PREFIX):
        return text
    text = text[len(PREFIX):]
    if SECTION not in text:
        raise ValueError('unrecognized generated module envelope')
    text = text.replace(SECTION, '', 1)
    return re.sub(r'^public import ', 'import ', text, flags=re.M)


def module_source(text):
    if text.startswith(PREFIX):
        return text
    imports = list(re.finditer(r'^import [\w.]+[^\S\n]*\n', text, re.M))
    if not imports:
        raise ValueError('generated module has no imports')
    split = imports[-1].end()
    header = re.sub(r'^import ', 'public import ', text[:split], flags=re.M)
    result = PREFIX + header + SECTION + text[split:]
    if len(result.splitlines()) > 10000:
        raise ValueError('generated source exceeds 10,000 physical lines')
    if unwrap(result) != text:
        raise AssertionError('visibility envelope changed the source body')
    return result


def rename_legacy(text):
    # These are the only H1 production tokens changed by the release's
    # American English identifier migration. String literals contain integers.
    return re.sub(r'\b(Catalogue|catalogueCheck|catalogue)\b',
                  lambda m: {'Catalogue': 'Catalog', 'catalogueCheck': 'catalogCheck',
                             'catalogue': 'catalog'}[m[0]], text)
