#!/usr/bin/env python3
"""Generate Lean exercise files from marked solution fragments."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


INLINE_START = "/- ex -/"
INLINE_END = "/- /ex -/"
DEFAULT_REPLACEMENT = "exercise"

LINE_START_RE = re.compile(r"([ \t]*)-- ex[ \t]*(\r?\n|$)")
LINE_END_RE = re.compile(r"^[ \t]*-- /ex[ \t]*(\r?\n|$)", re.MULTILINE)
LINE_START_FIND_RE = re.compile(r"^[ \t]*-- ex[ \t]*(?:\r?\n|$)", re.MULTILINE)


class MarkerError(Exception):
    pass


def at_line_start(text: str, index: int) -> bool:
    return index == 0 or text[index - 1] == "\n"


def format_line_replacement(indent: str, replacement: str, trailing_newline: str) -> str:
    lines = replacement.splitlines()
    if not lines:
        body = indent
    else:
        body = "\n".join(f"{indent}{line}" for line in lines)
    return f"{body}{trailing_newline}"


def previous_nonempty_line(text: str, index: int) -> str:
    for line in reversed(text[:index].splitlines()):
        if line.strip():
            return line
    return ""


def format_line_block_replacement(
    text: str, index: int, indent: str, replacement: str, trailing_newline: str
) -> str:
    # After `with`, Lean expects a case alternative rather than a standalone tactic.
    if previous_nonempty_line(text, index).rstrip().endswith("with"):
        return format_line_replacement(indent, f"| _ => {replacement}", trailing_newline)
    return format_line_replacement(indent, replacement, trailing_newline)


def check_no_nested_markers(text: str, start: int, end: int, context: str) -> None:
    inline_start = text.find(INLINE_START, start, end)
    if inline_start != -1:
        raise MarkerError(f"nested inline exercise marker in {context}")

    inline_end = text.find(INLINE_END, start, end)
    if inline_end != -1:
        raise MarkerError(f"unexpected inline exercise closing marker in {context}")

    line_start = LINE_START_FIND_RE.search(text, start, end)
    if line_start is not None:
        raise MarkerError(f"nested line exercise marker in {context}")


def replace_marked_fragments(text: str, replacement: str = DEFAULT_REPLACEMENT) -> tuple[str, int]:
    out: list[str] = []
    count = 0
    index = 0

    while index < len(text):
        if at_line_start(text, index):
            line_start = LINE_START_RE.match(text, index)
            if line_start is not None:
                content_start = line_start.end()
                line_end = LINE_END_RE.search(text, content_start)
                if line_end is None:
                    raise MarkerError("unmatched line exercise marker")

                check_no_nested_markers(text, content_start, line_end.start(), "line exercise block")
                out.append(
                    format_line_block_replacement(
                        text,
                        index,
                        line_start.group(1),
                        replacement,
                        line_end.group(1),
                    )
                )
                count += 1
                index = line_end.end()
                continue

            if LINE_END_RE.match(text, index) is not None:
                raise MarkerError("unexpected line exercise closing marker")

        if text.startswith(INLINE_START, index):
            content_start = index + len(INLINE_START)
            content_end = text.find(INLINE_END, content_start)
            if content_end == -1:
                raise MarkerError("unmatched inline exercise marker")

            check_no_nested_markers(text, content_start, content_end, "inline exercise block")
            out.append(replacement)
            count += 1
            index = content_end + len(INLINE_END)
            continue

        if text.startswith(INLINE_END, index):
            raise MarkerError("unexpected inline exercise closing marker")

        out.append(text[index])
        index += 1

    return "".join(out), count


def output_path(input_path: Path) -> Path:
    if input_path.suffix != ".lean":
        raise MarkerError(f"expected a .lean file, got {input_path}")
    return input_path.with_name(f"{input_path.stem}Exercises{input_path.suffix}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate <filename>Exercises.lean by replacing marked fragments with exercise."
    )
    parser.add_argument("file", type=Path, help="Lean source file to process")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    input_path = args.file

    try:
        text = input_path.read_text(encoding="utf-8")
        result, count = replace_marked_fragments(text)
        if count == 0:
            raise MarkerError(f"no exercise markers found in {input_path}")

        destination = output_path(input_path)
        destination.write_text(result, encoding="utf-8")
    except OSError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1
    except MarkerError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1

    print(f"wrote {destination} ({count} exercise fragment{'s' if count != 1 else ''})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
