#!/usr/bin/env python3
"""Compatibility entry point for the production H1 route."""


def main():
    from production_leaves import main as production_main
    production_main()


if __name__ == "__main__":
    main()
