import Lake
open Lake DSL

package «poly_decomp_reconfig» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «PolyDecompReconfig» where
  roots := #[`PolyDecompReconfig]
