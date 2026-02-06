#!/bin/bash

# Build script for LHL ECOOP Artifact
# This script generates the Makefile from _CoqProject and builds the project

set -e  # Exit on error

echo "========================================"
echo "LHL - Linearizability Hoare Logic"
echo "========================================"
echo ""

echo "[Step 1/2] Generating Makefile from _CoqProject..."
coq_makefile -f _CoqProject -o Makefile
echo "✓ Makefile generated successfully"
echo ""

echo "[Step 2/2] Building Coq project..."
echo "This may take several minutes depending on your system..."
echo ""

# Build with timing information
time make -j$(nproc 2>/dev/null || echo 2)

echo ""
echo "========================================"
echo "✓ Build completed successfully!"
echo "========================================"
echo ""