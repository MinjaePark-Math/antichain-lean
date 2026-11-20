"""Remove editorial color wrappers while retaining their complete TeX content."""
from __future__ import annotations

import re

AUTHOR_NAMES = ("minjae", "notea", "ai")
AUTHOR_TOKEN = re.compile(r"\\(?:minjae|notea|ai)\b")


def escaped(text, index):
    previous = index - 1
    while previous >= 0 and text[previous] == "\\":
        previous -= 1
    return (index - previous - 1) % 2 == 1


def uncomment_tex(text):
    """Blank comments without changing any original character/line offsets."""
    result = list(text)
    comment = False
    for index, char in enumerate(text):
        if char == "\n":
            comment = False
        elif comment:
            result[index] = " "
        elif char == "%" and not escaped(text, index):
            result[index] = " "
            comment = True
    return "".join(result)


def unwrap_author_markup(text, *, offsets=False):
    """Unwrap nested, braced editorial calls; never drop their argument text.

    Input comments are blanked first. The optional character map permits a
    correspondence review to locate the retained content in the original file.
    Malformed or unbraced editorial calls fail rather than losing source text.
    """
    active = uncomment_tex(text)
    output, positions = [], []

    def walk(first, last):
        index = first
        while index < last:
            match = AUTHOR_TOKEN.match(active, index)
            if match and not escaped(active, index):
                opening = match.end()
                while opening < last and active[opening].isspace():
                    opening += 1
                if opening == last or active[opening] != "{":
                    raise ValueError(f"Editorial command has no braced argument at {index}")
                depth, closing = 1, opening + 1
                while closing < last and depth:
                    if not escaped(active, closing):
                        if active[closing] == "{":
                            depth += 1
                        elif active[closing] == "}":
                            depth -= 1
                    closing += 1
                if depth:
                    raise ValueError(f"Unclosed editorial argument at {index}")
                # Removing a wrapper must not turn ``\log\minjae{S}``
                # into a new, undefined control word ``\logS``.
                if (opening + 1 < closing - 1 and active[opening + 1].isascii()
                        and active[opening + 1].isalpha()
                        and re.search(r"(?<!\\)\\[A-Za-z]+$", "".join(output[-128:]))):
                    output.append(" ")
                    positions.append(opening)
                walk(opening + 1, closing - 1)
                if (closing < last and active[closing].isascii() and active[closing].isalpha()
                        and re.search(r"(?<!\\)\\[A-Za-z]+$", "".join(output[-128:]))):
                    output.append(" ")
                    positions.append(closing - 1)
                index = closing
            else:
                output.append(active[index])
                positions.append(index)
                index += 1

    walk(0, len(active))
    result = "".join(output)
    return (result, positions) if offsets else result


def canonical_with_offsets(text):
    unwrapped, source_positions = unwrap_author_markup(text, offsets=True)
    result, positions = [], []
    for match in re.finditer(r"\s+|\S", unwrapped):
        token = " " if match.group().isspace() else match.group()
        if token == " " and not result:
            continue
        result.append(token)
        positions.append(source_positions[match.start()])
    if result and result[-1] == " ":
        result.pop()
        positions.pop()
    return "".join(result), positions


def canonical_tex(text):
    return " ".join(unwrap_author_markup(text).split())


def clean_companion_tex(text):
    """Remove standalone editorial definitions and unwrap all remaining calls."""
    definition = re.compile(
        r"^\s*\\(?:DeclareRobustCommand|newcommand|renewcommand|providecommand)\*?"
        r"\s*\{\\(?:minjae|notea|ai)\}"
    )
    lines = text.splitlines(keepends=True)
    retained = []
    for line in lines:
        if definition.match(line):
            # The manuscript currently uses isolated one-line definitions.
            # Reject future multiline definitions instead of deleting a prefix.
            depth = 0
            for index, char in enumerate(uncomment_tex(line)):
                if not escaped(line, index):
                    depth += (char == "{") - (char == "}")
            if depth:
                raise ValueError("A multiline editorial definition needs explicit review")
            retained.append("\n" if line.endswith("\n") else "")
        else:
            comment = next((index for index, char in enumerate(line)
                            if char == "%" and not escaped(line, index)), None)
            # A TeX comment consumes its end-of-line. Replacing a comment-only
            # line by an empty line would insert a paragraph inside displays.
            prefix = line if comment is None else line[:comment]
            if comment is not None and re.search(r"(?<!\\)\\[A-Za-z]+$", prefix):
                # A comment also terminates a control word. Preserve that
                # lexical boundary when its consumed newline is removed.
                prefix += " "
            retained.append(prefix)
    result = unwrap_author_markup("".join(retained))
    if AUTHOR_TOKEN.search(result):
        raise ValueError("Editorial markup survived cleaning")
    return "\n".join(line.rstrip() for line in result.splitlines()) + "\n"
