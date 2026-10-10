import Holant.Proofs.Traversal.MatchingExpansion.Orientation
import Holant.Proofs.Traversal.ArityTwo.TensorNetwork


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Factors
open Holant Holant.Tractable
open Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem small_oneHot {K : Type} [Zero K] {n : ℕ} (f : Signature K n) (hn : n ≤ 1) :
    Signature.OneHot f := by
  intro x hx
  have hw := Holant.weight_le x
  omega

theorem decomposition {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (fun _ g => Signature.OneHot g) f) (hz : f ≠ 0) :
    ∃ T : TensorDecomposition AlgebraicComplex n, (∀ i, Signature.OneHot (T.factor i)) ∧ T.value = f := by
  rcases hf with hzero | hT
  · exact (hz hzero).elim
  · exact hT

def data {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (fun _ g => Signature.OneHot g) f) : Data AlgebraicComplex n :=
  if hz : f = 0 then Data.zero n else Data.ofDecomposition (Classical.choose (decomposition f hf hz))

theorem data_exact {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (fun _ g => Signature.OneHot g) f) : (data f hf).value = f := by
  unfold data
  split
  · rename_i hz
    rw [Data.zero_value, hz]
  · rename_i hz
    exact (Classical.choose_spec (decomposition f hf hz)).2

theorem factor_oneHot {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (fun _ g => Signature.OneHot g) f) (j : Fin (data f hf).count) :
    Signature.OneHot ((data f hf).factor j) := by
  have hd : ∀ D : Data AlgebraicComplex n, D=data f hf →
      ∀ i, Signature.OneHot (D.factor i) := by
    intro D hD
    by_cases hz : f=0
    · have hD' : D=Data.zero n := hD.trans (dif_pos hz)
      clear hD
      subst D
      intro i
      exact small_oneHot _ (Nat.le_refl 1)
    · have hD' : D=Data.ofDecomposition
          (Classical.choose (decomposition f hf hz)) := hD.trans (dif_neg hz)
      clear hD
      subst D
      intro i
      exact (Classical.choose_spec (decomposition f hf hz)).1 i
  exact hd _ rfl j

theorem vertex_oneHot {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (fun _ g => Signature.OneHot g) f) (v : (data f hf).Vertex) :
    Signature.OneHot ((data f hf).finite.vertex v) := by
  cases v with
  | none => exact small_oneHot _ (Nat.zero_le _)
  | some j => exact factor_oneHot f hf j

theorem network_exact {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (fun _ g => Signature.OneHot g) f) : (data f hf).network.denote = f :=
  (Data.network_denote _).trans (data_exact f hf)

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Factors
