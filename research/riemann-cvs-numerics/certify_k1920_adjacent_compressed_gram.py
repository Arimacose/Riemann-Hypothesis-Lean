#!/usr/bin/env python3
"""Compatibility entry point for the historical K=1920 certificate command."""

from certify_adjacent_compressed_gram import _roots_and_poles, certify, main

__all__ = ["_roots_and_poles", "certify", "main"]


if __name__ == "__main__":
    raise SystemExit(main())
