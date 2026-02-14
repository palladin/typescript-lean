#!/bin/bash
# Fetch TypeScript conformance test files from GitHub.
# Downloads a tarball and extracts only the scanner/parser tests + baselines.

set -e

REPO="microsoft/TypeScript"
BRANCH="main"
DEST="testdata/TypeScript"
TARBALL_URL="https://github.com/$REPO/archive/refs/heads/$BRANCH.tar.gz"
TMPDIR=$(mktemp -d)

echo "Fetching TypeScript test files from $REPO ($BRANCH)..."
echo "Downloading tarball (this may take a moment)..."

# Download and extract only the paths we need
curl -sL "$TARBALL_URL" | tar xz -C "$TMPDIR" \
  --include="TypeScript-main/tests/cases/conformance/scanner/*" \
  --include="TypeScript-main/tests/cases/conformance/parser/*" \
  2>/dev/null || true

echo "Extracting test files..."
mkdir -p "$DEST/tests/cases/conformance"
if [ -d "$TMPDIR/TypeScript-main/tests/cases/conformance/scanner" ]; then
  cp -r "$TMPDIR/TypeScript-main/tests/cases/conformance/scanner" "$DEST/tests/cases/conformance/"
fi
if [ -d "$TMPDIR/TypeScript-main/tests/cases/conformance/parser" ]; then
  cp -r "$TMPDIR/TypeScript-main/tests/cases/conformance/parser" "$DEST/tests/cases/conformance/"
fi

# Now fetch baselines for these test files
echo "Fetching baselines for test files..."

# Collect all test names
test_names=()
while IFS= read -r f; do
  name=$(basename "$f" .ts)
  name=${name%.tsx}
  test_names+=("$name")
done < <(find "$DEST/tests/cases/conformance" -name "*.ts" -o -name "*.tsx")

echo "Found ${#test_names[@]} test files, downloading baselines..."

# Download baselines tarball and extract matching files
# Since baselines dir is huge, we'll download the full tarball path
# but filter to only our test names
curl -sL "$TARBALL_URL" | tar xz -C "$TMPDIR" \
  --include="TypeScript-main/tests/baselines/reference/*" \
  2>/dev/null || true

if [ -d "$TMPDIR/TypeScript-main/tests/baselines/reference" ]; then
  mkdir -p "$DEST/tests/baselines/reference"

  # Only copy baselines that match our test names
  for name in "${test_names[@]}"; do
    for f in "$TMPDIR/TypeScript-main/tests/baselines/reference/${name}"*; do
      [ -f "$f" ] && cp "$f" "$DEST/tests/baselines/reference/"
    done
  done
fi

# Cleanup
rm -rf "$TMPDIR"

echo ""
echo "Done. Test files in $DEST/"
scanner_count=$(find "$DEST/tests/cases/conformance/scanner" -name "*.ts" 2>/dev/null | wc -l | tr -d ' ')
parser_count=$(find "$DEST/tests/cases/conformance/parser" -name "*.ts" 2>/dev/null | wc -l | tr -d ' ')
baseline_count=$(find "$DEST/tests/baselines" -type f 2>/dev/null | wc -l | tr -d ' ')
echo "  Scanner tests:  $scanner_count"
echo "  Parser tests:   $parser_count"
echo "  Baseline files: $baseline_count"
