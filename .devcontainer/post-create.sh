#!/bin/bash
# Post-create script for Lean 4 DevContainer
# This script runs after the container is created.

set -e

echo "=== Lean 4 DevContainer Setup ==="

# 1. Install the toolchain specified in lean-toolchain
TOOLCHAIN=$(cat lean-toolchain | tr -d '[:space:]')
echo "Installing toolchain: $TOOLCHAIN"
elan default "$TOOLCHAIN"

# 2. Update lake dependencies
echo "Updating lake dependencies..."
lake update

# 3. If Mathlib is a dependency, fetch precompiled cache
if grep -q "mathlib" lakefile.lean 2>/dev/null || grep -q "mathlib" lakefile.toml 2>/dev/null; then
    echo "Mathlib detected as dependency. Fetching precompiled cache..."
    echo "This may take a few minutes on first run."
    lake exe cache get || echo "WARNING: cache get failed. You may need to build Mathlib from source."
fi

# 4. Lean LSP MCP
if command -v uvx >/dev/null 2>&1; then
    echo "Pre-fetching lean-lsp-mcp via uvx..."
    uvx --help >/dev/null 2>&1 || true
    uvx lean-lsp-mcp --help >/dev/null 2>&1 || echo "NOTE: could not pre-fetch lean-lsp-mcp (it will be fetched on first use)."
fi

echo ""
echo "=== Setup Complete ==="
echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"
echo "uv version:   $(uv --version)"
