import Holant.Proofs.Dichotomy.Retained.StableDenseResidualPencil
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualAlgebra
import Holant.Marked.SupportAtlas.ComplementForm

/-! Three genuine ordered cap pencils force the same complementary product
in every parity-compatible flip chart, including originally odd support. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualCharts
open Holant Holant.Projective Holant.Marked.SupportAtlas
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open StableDenseResidualPencil StableDenseResidualAlgebra

private theorem fill_id (a p b c : Bool) :
    fill (Equiv.refl _) a p b c = ![a,a ^^ p,b,c] := by
  rfl

private theorem fill_12 (a p b c : Bool) :
    fill (Equiv.swap (1 : Fin 4) 2) a p b c = ![a,b,a ^^ p,c] := by
  funext i
  fin_cases i <;> simp [fill,Equiv.swap_apply_def]

private theorem fill_13 (a p b c : Bool) :
    fill (Equiv.swap (1 : Fin 4) 3) a p b c = ![a,c,b,a ^^ p] := by
  funext i
  fin_cases i <;> simp [fill,Equiv.swap_apply_def]

private theorem xor_vec (x y : Holant.Marked.SupportAtlas.Word) :
    xorWord x y = ![x 0 ^^ y 0,x 1 ^^ y 1,x 2 ^^ y 2,x 3 ^^ y 3] := by
  funext i
  fin_cases i <;> rfl

/-- The complete-group phase samples imply exact original-table equations,
simultaneously in every chart of the supported parity. There is no
cancellation premise and no assumption of an eight-vertex dichotomy. -/
theorem chart_products {m : ℕ} (hm : 3 ≤ m) (q : Signature ℂ 4)
    (deck : SafeDeck m 1 q) (p : Bool)
    (full : ∀ x, q x ≠ 0 ↔ parity x = p)
    (mask : Holant.Marked.SupportAtlas.Word) (same : parity mask = p) :
    Products (fun x => q (xorWord x mask)) := by
  have live0 (a : Bool) :
      q (fill (Equiv.refl _) a (mask 0 ^^ mask 1) false (mask 2 ^^ mask 3)) ≠ 0 := by
    apply (full _).mpr
    rw [← same,fill_id]
    cases a <;> cases h0 : mask 0 <;> cases h1 : mask 1 <;>
      cases h2 : mask 2 <;> cases h3 : mask 3 <;> simp [parity,h0,h1,h2,h3]
  have live1 (a : Bool) :
      q (fill (Equiv.swap (1 : Fin 4) 2) a (mask 0 ^^ mask 2) false
        (mask 1 ^^ mask 3)) ≠ 0 := by
    apply (full _).mpr
    rw [← same,fill_12]
    cases a <;> cases h0 : mask 0 <;> cases h1 : mask 1 <;>
      cases h2 : mask 2 <;> cases h3 : mask 3 <;> simp [parity,h0,h1,h2,h3]
  have live2 (a : Bool) :
      q (fill (Equiv.swap (1 : Fin 4) 3) a (mask 0 ^^ mask 3) false
        (mask 2 ^^ mask 1)) ≠ 0 := by
    apply (full _).mpr
    rw [← same,fill_13]
    cases a <;> cases h0 : mask 0 <;> cases h1 : mask 1 <;>
      cases h2 : mask 2 <;> cases h3 : mask 3 <;> simp [parity,h0,h1,h2,h3]
  have d0 := dense_slice_product hm q deck (Equiv.refl _) (mask 0 ^^ mask 1)
    (mask 2 ^^ mask 3) (live0 false) (live0 true)
  have d1 := dense_slice_product hm q deck (Equiv.swap (1 : Fin 4) 2)
    (mask 0 ^^ mask 2) (mask 1 ^^ mask 3) (live1 false) (live1 true)
  have d2 := dense_slice_product hm q deck (Equiv.swap (1 : Fin 4) 3)
    (mask 0 ^^ mask 3) (mask 2 ^^ mask 1) (live2 false) (live2 true)
  clear full deck live0 live1 live2 same
  cases h0 : mask 0 <;> cases h1 : mask 1 <;>
    cases h2 : mask 2 <;> cases h3 : mask 3 <;>
    simp [-fill_eq_join,Products,entries,xor_vec,fill_id,fill_12,fill_13,h0,h1,h2,h3] at d0 d1 d2 ⊢ <;>
    grind only [mul_comm]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualCharts
end
