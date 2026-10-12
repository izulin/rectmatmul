import Lake
open Lake DSL

package rectmatmulLean where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require matrixMultiplicationAllFields from git
  "https://github.com/PalomarArchive/selanavot--matrix-multiplication-all-fields--d4d6744d47b0.git"
  @ "8375e73ed454e3128500d10d87480c5dd597ff03"

@[default_target]
lean_lib Rectangular
