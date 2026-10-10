import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars
import Holant.Proofs.Reductions.GeneralExtraction.GeneralPowerExposure
import Holant.OpenNetworkComposition.ProjectiveSubstitution


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
open Holant.LocalDrafts.Hardness.GeneralExtraction
noncomputable section
variable {L : Type*} [Field L]

theorem realizes_reindex_equiv {m n : ℕ} (F : SignatureFamily L)
    (e : Fin m ≃ Fin n) (f : Signature L m)
    (hf : Gadget.Realizes F .disequality f) :
    Gadget.Realizes F .disequality (Tensor.reindex e f) := by
  have hmn : m = n := by simpa using Fintype.card_congr e
  subst n
  exact Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f hf e.symm

def ProperSplit.grouped {f a b : AnySignature L} (s : ProperSplit f a b) :
    Signature L (a.1 + b.1) :=
  Tensor.reindex (s.ports.symm.trans finSumFinEquiv) f.2

def ProperSplit.scaledRight {f a b : AnySignature L} (s : ProperSplit f a b) :
    Signature L b.1 := fun x => (s.scale : L) * b.2 x

theorem ProperSplit.grouped_eq {f a b : AnySignature L} (s : ProperSplit f a b) :
    s.grouped = Signature.tensor a.2 s.scaledRight := by
  funext x
  simp only [ProperSplit.grouped, Tensor.reindex, Equiv.trans_apply]
  rw [s.equation]
  simp only [Equiv.symm_apply_apply, Signature.tensor_apply, ProperSplit.scaledRight,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  ring

theorem ProperSplit.scaledRight_nonzero {f a b : AnySignature L}
    (s : ProperSplit f a b) (hf : f.2 ≠ 0) : s.scaledRight ≠ 0 :=
  smul_ne_zero s.scale.ne_zero (s.factors_nonzero hf).2

theorem ProperSplit.grouped_realizes {f a b : AnySignature L}
    (s : ProperSplit f a b) (F : SignatureFamily L)
    (hf : Gadget.Realizes F .disequality f.2) :
    Gadget.Realizes F .disequality s.grouped :=
  realizes_reindex_equiv F (s.ports.symm.trans finSumFinEquiv) f.2 hf

theorem mixedSupport_mono {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hF : GeneralCarrierExistence.MixedSupport F) :
    GeneralCarrierExistence.MixedSupport G := by
  intro b
  obtain ⟨n, f, hf, x, hx, hb⟩ := hF b
  exact ⟨n, f, hFG hf, x, hx, hb⟩

/-- In this source stratum the literal anchor I already supplies both
charge signs: use its two constant supported words. This is not inferred
from torsion or from the merely structural native X edge box. -/
theorem mixedSupport_of_identity (F : SignatureFamily L) (hI : RetainsIdentity F) :
    GeneralCarrierExistence.MixedSupport F := by
  intro b
  refine ⟨2, OrdinaryNormalization.identitySignature, hI, (fun _ => b), ?_, ?_⟩
  · simp [OrdinaryNormalization.identitySignature, Signature.equality]
  · norm_num [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance]

/-- Actual exposure of a positive tensor power of the LEFT factor of this
specific retained split. Both the carrier multiplier and substitution
multiplier are retained; the final ordinary graph uses only original F.
The general carrier proof is reused, not postulated or reimplemented. -/
theorem ProperSplit.left_power_ordinary {f a b : AnySignature L}
    (s : ProperSplit f a b) (F : SignatureFamily L)
    (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (hs : GeneralCarrierExistence.MixedSupport F)
    (hf : f.2 ≠ 0) (ha : Gadget.Realizes F .disequality f.2) :
    ∃ r : ℕ, 0 < r ∧ ∃ c : L, c ≠ 0 ∧ ∃ N : Network L (r * a.1),
      (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature L) ∈ F) ∧
      (∀ e, N.edge e = Signature.disequality) ∧
      N.denote = fun x => c * Carrier.blockPower a.2 r x := by
  let G : SignatureFamily L := insert ⟨a.1 + b.1, s.grouped⟩ F
  have hFG : F ⊆ G := Set.subset_insert _ _
  have htensor : (⟨a.1 + b.1, Signature.tensor a.2 s.scaledRight⟩ : AnySignature L) ∈ G := by
    rw [← s.grouped_eq]
    exact Set.mem_insert _ _
  obtain ⟨r, hr, c, hc, N, hU, hX, hvalue⟩ :=
    GeneralPowerExposure.ordinary_power G htwo (mixedSupport_mono hFG hs)
      a.2 s.scaledRight s.right_pos (s.scaledRight_nonzero hf) htensor
  have hlabels : ∀ g ∈ G, Gadget.Realizes F .disequality g.2 := by
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact s.grouped_realizes F ha
    · exact Gadget.realizes_of_mem F .disequality g.2 hg
  obtain ⟨d, hd, hactual⟩ := realizes_network_upTo F N
    (fun v => hlabels _ (hU v)) hX htwo
  obtain ⟨M, hM, hMX, hMv⟩ := OrdinaryNormalization.realizes_exists_ordinary hI hactual
  refine ⟨r, hr, d * c, mul_ne_zero hd hc, M, hM, hMX, ?_⟩
  rw [hMv, hvalue]
  funext x
  exact (mul_assoc d c _).symm

/-- Swapping the split keeps the same unit and literally swaps its disjoint
port blocks, so right-factor provenance does not require a new theorem. -/
def ProperSplit.swap {f a b : AnySignature L} (s : ProperSplit f a b) :
    ProperSplit f b a where
  left_pos := s.right_pos
  right_pos := s.left_pos
  ports := (Equiv.sumComm _ _).trans s.ports
  scale := s.scale
  equation := by
    rw [s.equation]
    funext x
    change (s.scale : L) * (a.2 _ * b.2 _) = (s.scale : L) * (b.2 _ * a.2 _)
    rw [mul_comm (a.2 _) (b.2 _)]
    rfl

theorem ProperSplit.right_power_ordinary {f a b : AnySignature L}
    (s : ProperSplit f a b) (F : SignatureFamily L)
    (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (hs : GeneralCarrierExistence.MixedSupport F)
    (hf : f.2 ≠ 0) (ha : Gadget.Realizes F .disequality f.2) :
    ∃ r : ℕ, 0 < r ∧ ∃ c : L, c ≠ 0 ∧ ∃ N : Network L (r * b.1),
      (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature L) ∈ F) ∧
      (∀ e, N.edge e = Signature.disequality) ∧
      N.denote = fun x => c * Carrier.blockPower b.2 r x :=
  s.swap.left_power_ordinary F hI htwo hs hf ha

/-- Direct bridge to the hardness worker's existing labelled PowerMacro.
All labels are picked from G itself, including after eliminating the
temporary grouped-parent label by actual gadget substitution. -/
theorem ProperSplit.left_power_labelled {f a b : AnySignature L}
    (s : ProperSplit f a b) {k : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin k) → Signature L (arity i.val))
    (hI : RetainsIdentity (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature L))))
    (htwo : (2 : L) ≠ 0)
    (hs : GeneralCarrierExistence.MixedSupport
      (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature L))))
    (hf : f.2 ≠ 0)
    (ha : Gadget.Realizes (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature L)))
      .disequality f.2) : Nonempty (GeneralPowerExposure.PowerMacro G a.2) := by
  obtain ⟨r, hr, c, hc, N, hv, he, hN⟩ := s.left_power_ordinary _ hI htwo hs hf ha
  let lab := Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses arity G N hv (0 : Fin 1)
  refine ⟨⟨r, hr, c, hc, N, lab, ?_⟩⟩
  exact (Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses_denote
    arity G N hv he (0 : Fin 1) (fun _ => Signature.disequality) rfl).trans hN

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
