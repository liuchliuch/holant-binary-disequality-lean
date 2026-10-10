import Holant.Proofs.Hardness.EightVertexGaugeMixedPairs
import Holant.Proofs.Hardness.EightVertexGaugePorts

/-! Different fourth-power anchors for two individually uniform gauge rows
force a live two-row gadget whose actual complete phase deck is unsafe. Port
selection and both native wiring orientations are explicit; no unary resource
or desired complexity conclusion is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeMixedPencil
open Holant Holant.Marked.SupportAtlas
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugeTwoRowAlgebra EightVertexGaugeTwoRowPencil EightVertexGaugePorts

private theorem choose_internal (i j : Fin 4) (different : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 4), e.symm 2 = i ∧ e.symm 3 = j := by
  have all : ∀ i j : Fin 4, i ≠ j →
      ∃ e : Equiv.Perm (Fin 4), e.symm 2 = i ∧ e.symm 3 = j := by decide
  exact all i j different

/-- This compares two rows without asserting a common basis in advance. -/
theorem unsafe_deck {m : ℕ} (hm : 3 ≤ m) (a b : ℂ) (u v : Fin 4 → ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (sameU : ∀ i, u i ^ 4 = u 0 ^ 4) (sameV : ∀ i, v i ^ 4 = v 0 ^ 4)
    (different : u 0 ^ 4 ≠ v 0 ^ 4) :
    ∃ (e f : Equiv.Perm (Fin 4)) (cross : Bool), ¬ SafeDeck m 1
      (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted b v) e f cross).denote := by
  obtain ⟨i,j,k,l,hij,hkl,hE,hO⟩ := EightVertexGaugeMixedPairs.live_pair u v hu hv different
  obtain ⟨e,he2,he3⟩ := choose_internal i j hij
  obtain ⟨f,hf2,hf3⟩ := choose_internal k l hkl
  let U := fun r => u (e.symm r)
  let V := fun r => v (f.symm r)
  have hU : ∀ r, U r ≠ 0 := fun r => hu _
  have hV : ∀ r, V r ≠ 0 := fun r => hv _
  have liveE : evenFactor U V ≠ 0 := by
    simpa [evenFactor,U,V,he2,he3,hf2,hf3] using hE
  have squares (r s : Fin 4) : U r ^ 2 ≠ V s ^ 2 := by
    intro equal
    have fourth : U r ^ 4 = V s ^ 4 := by
      calc
        U r ^ 4 = (U r ^ 2)^2 := by ring
        _ = (V s ^ 2)^2 := congrArg (fun z : ℂ => z^2) equal
        _ = V s ^ 4 := by ring
    exact different ((sameU _).symm.trans (fourth.trans (sameV _)))
  have fail (cross : Bool) (liveO : oddFactor U V cross ≠ 0) :
      ¬ SafeDeck m 1
        (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted b v) e f cross).denote := by
    rw [onPorts_output]
    intro deck
    have equal := safe_output_factors hm a b U V cross ha hb hU hV liveE liveO deck
    have zero := sub_eq_zero.mpr equal
    cases cross
    · rw [straight_factor] at zero
      exact (mul_ne_zero (sub_ne_zero.mpr (squares 2 2))
        (sub_ne_zero.mpr (squares 3 3))) zero
    · rw [crossed_factor] at zero
      exact (mul_ne_zero (sub_ne_zero.mpr (squares 2 3))
        (sub_ne_zero.mpr (squares 3 2))) zero
  rcases hO with hO | hO
  · refine ⟨e,f,true,fail true ?_⟩
    simpa [oddFactor,U,V,he2,he3,hf2,hf3] using hO
  · refine ⟨e,f,false,fail false ?_⟩
    simpa [oddFactor,U,V,he2,he3,hf2,hf3] using hO

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeMixedPencil
end
