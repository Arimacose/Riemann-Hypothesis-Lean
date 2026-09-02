#!/usr/bin/env python3
"""Compatibility entry point for the historical K=1920 shift-cell command."""

from certify_adjacent_adi_shift_cells import certify, main

__all__ = ["certify", "main"]


if __name__ == "__main__":
    raise SystemExit(main())
