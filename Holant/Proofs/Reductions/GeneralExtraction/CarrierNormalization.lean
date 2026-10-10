import Holant.Proofs.Reductions.GeneralExtraction.GeneralCarrierExistence
import Holant.Proofs.Reductions.GeneralExtraction.Carrier
import Holant.Complexity.ClosedNetworkSerialize


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.CarrierNormalization
open GeneralCarrierExistence

variable {K : Type*} [Field K] {n m : ℕ} {F : SignatureFamily K}
variable {g : Signature K n} (W : Witness F g)

abbrev Background := {v : Fin W.graph.shape.vertices // W.factor v = false}
abbrev Factor := {v : Fin W.graph.shape.vertices // W.factor v = true}
abbrev count := Fintype.card (Factor W)
abbrev arity (v : Background W) := W.graph.shape.arity v.val
abbrev background (v : Background W) := W.graph.vertex v.val

theorem count_positive : 0 < count W := by
  obtain ⟨v, hv⟩ := W.factor_present
  exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩

def vertices : Carrier.OldVertex (Background W) 0 (count W) ≃ Fin W.graph.shape.vertices where
  toFun v := match v with
    | .inl v => v.val
    | .inr (.inl v) => Fin.elim0 v
    | .inr (.inr (.inl v)) => Fin.elim0 v
    | .inr (.inr (.inr v)) => ((Fintype.equivFin (Factor W)).symm v).val
  invFun v := if h : W.factor v = true then
      .inr (.inr (.inr ((Fintype.equivFin (Factor W)) ⟨v, h⟩)))
    else .inl ⟨v, by cases he : W.factor v <;> simp_all⟩
  left_inv := by
    rintro (v | (v | (v | v)))
    · simp [v.property]
    · exact Fin.elim0 v
    · exact Fin.elim0 v
    · simp [((Fintype.equivFin (Factor W)).symm v).property]
  right_inv := by
    intro v
    by_cases h : W.factor v = true <;> simp [h]

theorem factor_arity (v : Factor W) : W.graph.shape.arity v.val = n :=
  congrArg Sigma.fst (W.factor_label v.val v.property)

theorem arity_eq (v : Carrier.OldVertex (Background W) 0 (count W)) :
    Carrier.oldArity (arity W) m n v = W.graph.shape.arity (vertices W v) := by
  rcases v with v | (v | (v | v))
  · rfl
  · exact Fin.elim0 v
  · exact Fin.elim0 v
  · exact (factor_arity W ((Fintype.equivFin (Factor W)).symm v)).symm

def ports : Carrier.OldPort (arity W) m n 0 (count W) ≃
    (Σ v : Fin W.graph.shape.vertices, Fin (W.graph.shape.arity v)) :=
  Equiv.sigmaCongr (vertices W) (fun v => finCongr (arity_eq (m := m) W v))

def wiring : Carrier.Wiring (arity W) m n 0 (count W) (Fin W.graph.shape.edges) :=
  ⟨(ports W).trans (Holant.Complexity.ClosedLabelling.closedPortEquiv W.graph.shape)⟩

theorem sigma_value {a b : ℕ} {u : Signature K a} {v : Signature K b}
    (h : (⟨a, u⟩ : AnySignature K) = ⟨b, v⟩) (x : Fin a → Bool) :
    u x = v (fun i => x (Fin.cast (congrArg Sigma.fst h).symm i)) := by
  cases h
  rfl

theorem vertex_value (f : Signature K m)
    (v : Carrier.OldVertex (Background W) 0 (count W))
    (x : Fin (W.graph.shape.arity (vertices W v)) → Bool) :
    (Carrier.original (arity W) (wiring W) (background W) f g
      (fun _ => Signature.disequality)).vertex v
        (fun i => x (Fin.cast (arity_eq W v) i)) = W.graph.vertex (vertices W v) x := by
  rcases v with v | (v | (v | v))
  · rfl
  · exact Fin.elim0 v
  · exact Fin.elim0 v
  · exact (sigma_value (W.factor_label _ ((Fintype.equivFin (Factor W)).symm v).property) x).symm

/-- The original assignment sum is invariant under the explicit carrier
normalization. The discarded factor is g; the surviving f has no old vertices. -/
theorem normalized_denote (f : Signature K m) :
    (Carrier.original (arity W) (wiring W) (background W) f g
      (fun _ => Signature.disequality)).denote Fin.elim0 = W.graph.denote Fin.elim0 := by
  classical
  unfold FiniteNetwork.denote Network.denote
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv (vertices W)
    intro v
    rw [← vertex_value W f v (W.graph.shape.assignment Fin.elim0 z (vertices W v))]
    congr 1
    funext i
    change z (Holant.Complexity.ClosedLabelling.closedPortEquiv W.graph.shape
      ⟨vertices W v, Fin.cast (arity_eq W v) i⟩) = _
    cases he : W.graph.shape.ports ⟨vertices W v, Fin.cast (arity_eq W v) i⟩ with
    | inl a => exact Fin.elim0 a
    | inr a => simp [Holant.Complexity.ClosedLabelling.closedPortEquiv,
        Holant.Complexity.RawClosedNetwork.closedEndsEquiv, NetworkShape.assignment, he]
  · apply Finset.prod_congr rfl
    intro e _
    rw [W.native e]
    rfl

/-- The scalar used by the existing carrier surgery is now proved nonzero
from the constructed witness. It is no longer a top-level premise. -/
theorem normalized_nonzero (f : Signature K m) :
    (Carrier.original (arity W) (wiring W) (background W) f g
      (fun _ => Signature.disequality)).denote Fin.elim0 ≠ 0 := by
  rw [normalized_denote W f]
  exact W.nonzero

theorem extracted_value (f : Signature K m) (x : Fin (count W * m) → Bool) :
    (Carrier.extracted (arity W) (wiring W) (background W) f g
      (fun _ => Signature.disequality)).toNetwork.denote x =
        W.graph.denote Fin.elim0 * Carrier.blockPower f (count W) x := by
  rw [FiniteNetwork.denote_toNetwork, Carrier.extracted_denote, normalized_denote W f]

/-- Original retained background labels are preserved by normalization. -/
theorem background_mem (v : Background W) :
    (⟨arity W v, background W v⟩ : AnySignature K) ∈ F :=
  W.background_label v.val v.property

end Holant.LocalDrafts.Hardness.GeneralExtraction.CarrierNormalization
