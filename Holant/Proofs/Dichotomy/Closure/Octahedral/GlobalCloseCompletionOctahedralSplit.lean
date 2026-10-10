import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTransport

/-! Coefficient extraction from the preserved marked-octahedral proof. The SAME physical transfer map reconstructs a real
2|2 split of the SAME original ordered q4, after undoing its literal X.
The two binary factors descend to original L through the existing exact
pivot-ratio producer, preserving the exact partition and both arities.
This is coefficient descent, not an assertion of factor gadget access. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open scoped BigOperators Matrix

private theorem binary_nonzero (U : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) (hd : U.det ≠ 0) :
    Holant.Projective.BoundedTorsion.binarySignature U ≠ (0 : Signature ℂ 2) := by
  intro hz
  have he : U = 0 := by
    ext a b
    change U a b=(0 : ℂ)
    have hh := congrFun hz ![a,b]
    simpa only [Holant.Projective.BoundedTorsion.binarySignature,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] using hh
  exact hd (by rw [he]; simp)

/-- A crossing matching split on the original ports, not only a
reconstruction of an independently proposed coefficient matrix. -/
theorem rankFour_complex_split (f : Form) (q : FourTensor) (e : PortOrder)
    (hr : (transferMatrix q e).rank = 4)
    (h : OneSided (Roots f) (transferMatrix q e)) :
    ∃ ports : (Fin 2 ⊕ Fin 2) ≃ Fin 4, ∃ u v : Signature ℂ 2,
      u ≠ 0 ∧ v ≠ 0 ∧ q = Tensor.reindex ports (Tensor.tensor u v) := by
  have hd := (rank_four_iff_det_ne_zero _).mp hr
  obtain ⟨i,c,hc,ha⟩ := marked_candidate_coverage f _ hd h
  obtain ⟨U,W,hU,hW,he⟩ := markedCandidate_normal_forms f i c hc
  rw [←ha] at he
  have hc : cardMatrix (relabel e q) = rightX*transferMatrix q e := by
    rw [transferMatrix,←Matrix.mul_assoc,rightX_square,Matrix.one_mul]
  have hX : (Holant.Certificates.MatchingContractionClosure.X : Holant.Certificates.TetrahedralPreservers.BinaryMatrix).det ≠ 0 :=
    (direction_X f).det_ne_zero
  have hWX : (W*Holant.Certificates.MatchingContractionClosure.X).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hW hX
  have restore : Tensor.reindex e (relabel e q) = q := by
    change Tensor.reindex e (Tensor.reindex e.symm q)=q
    simp only [Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl]
  rcases he with he | he
  · have hq : relabel e q = P1 U.transpose (W*Holant.Certificates.MatchingContractionClosure.X) := by
      calc
        relabel e q = reconstruct (cardMatrix (relabel e q)) := (reconstruct_cardMatrix _).symm
        _ = _ := by rw [hc,he,rightX,sandwich_comp,Matrix.one_mul,reconstruct_sandwich]
    refine ⟨(finSumFinEquiv.trans
      (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralClassifier.matchingFrame 1)).trans e,
      Holant.Projective.BoundedTorsion.binarySignature U.transpose,Holant.Projective.BoundedTorsion.binarySignature (W*Holant.Certificates.MatchingContractionClosure.X),
      binary_nonzero _ (by simpa only [Matrix.det_transpose] using hU),
      binary_nonzero _ hWX,?_⟩
    calc
      q = Tensor.reindex e (P1 U.transpose (W*Holant.Certificates.MatchingContractionClosure.X)) := by
        rw [←hq]; exact restore.symm
      _ = _ := by
        change Tensor.reindex e (matchingProduct 1 _ _) = _
        rw [Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrent.matching_tensor,
          Tensor.reindex_trans]
  · have hq : relabel e q = P2 (W*Holant.Certificates.MatchingContractionClosure.X) U.transpose := by
      calc
        relabel e q = reconstruct (cardMatrix (relabel e q)) := (reconstruct_cardMatrix _).symm
        _ = _ := by
          rw [hc,he,rightX]
          have hh : sandwich 1 Holant.Certificates.MatchingContractionClosure.X*transposeSandwich U W =
              transposeSandwich U (W*Holant.Certificates.MatchingContractionClosure.X) := by
            simpa only [kindSandwich,ite_true,Matrix.one_mul] using
              sandwich_kind_comp true 1 Holant.Certificates.MatchingContractionClosure.X U W
          rw [hh,reconstruct_transposeSandwich]
    refine ⟨(finSumFinEquiv.trans
      (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralClassifier.matchingFrame 2)).trans e,
      Holant.Projective.BoundedTorsion.binarySignature (W*Holant.Certificates.MatchingContractionClosure.X),Holant.Projective.BoundedTorsion.binarySignature U.transpose,
      binary_nonzero _ hWX,binary_nonzero _ (by simpa only [Matrix.det_transpose] using hU),?_⟩
    calc
      q = Tensor.reindex e (P2 (W*Holant.Certificates.MatchingContractionClosure.X) U.transpose) := by
        rw [←hq]; exact restore.symm
      _ = _ := by
        change Tensor.reindex e (matchingProduct 2 _ _) = _
        rw [Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrent.matching_tensor,
          Tensor.reindex_trans]

/-- Specialize the existing pivot-ratio descent to the actual two binary
blocks, so the public conclusion explicitly retains arity2 and the ports. -/
theorem binary_split_descends {L : Type} [Field L] (φ : L →+* ℂ)
    (q : Signature L 4) (hq : q ≠ 0) (ports : (Fin 2 ⊕ Fin 2) ≃ Fin 4)
    (u v : Signature ℂ 2)
    (he : (fun x => φ (q x)) = Tensor.reindex ports (Tensor.tensor u v)) :
    ∃ a b : Signature L 2, a ≠ 0 ∧ b ≠ 0 ∧ q = Tensor.reindex ports (Tensor.tensor a b) := by
  let join : (Fin 2 → Bool) → (Fin 2 → Bool) → (Fin 4 → Bool) :=
    fun x y i => Sum.elim x y (ports.symm i)
  let table := fun x y => q (join x y)
  have hword (x : Fin 4 → Bool) :
      join (fun i => x (ports (.inl i))) (fun j => x (ports (.inr j))) = x := by
    funext i
    have hh (z : Fin 2 ⊕ Fin 2) :
        Sum.elim (fun j => x (ports (.inl j))) (fun j => x (ports (.inr j))) z = x (ports z) := by
      cases z <;> rfl
    exact (hh (ports.symm i)).trans (congrArg x (ports.apply_symm_apply i))
  have ht : table ≠ 0 := by
    intro hz
    apply hq
    funext x
    have hh := congrFun (congrFun hz (fun i => x (ports (.inl i))))
      (fun j => x (ports (.inr j)))
    simpa only [table,hword,Pi.zero_apply] using hh
  have hc : ∀ x y, φ (table x y) = u x*v y := by
    intro x y
    have hh := congrFun he (join x y)
    simpa [table,join,Tensor.reindex,Tensor.tensor] using hh
  obtain ⟨a,b,ha,hb,hab⟩ := Holant.Algebraic.FactorDescent.exists_exact_factorization
    φ table u v hc ht
  refine ⟨a,b,ha,hb,?_⟩
  funext x
  have hh := hab (fun i => x (ports (.inl i))) (fun j => x (ports (.inr j)))
  simpa only [table,hword,Tensor.reindex,Tensor.tensor] using hh

theorem original_prime_no_rankFour {L : Type} [Field L] (φ : L →+* ℂ)
    (q : Signature L 4) (hp : Prime (⟨4,q⟩ : AnySignature L))
    (f : Form) (e : PortOrder)
    (h : OneSided (Roots f) (transferMatrix (RingHomRealization.mapSignature φ q) e)) :
    (transferMatrix (RingHomRealization.mapSignature φ q) e).rank ≠ 4 := by
  intro hr
  obtain ⟨ports,u,v,hu,hv,he⟩ := rankFour_complex_split f _ e hr h
  obtain ⟨a,b,ha,hb,hab⟩ := binary_split_descends φ q hp.1 ports u v he
  exact hp.2 ⟨⟨2,a⟩,⟨2,b⟩,⟨{
    left_pos := by change 0<2; decide
    right_pos := by change 0<2; decide
    ports := ports
    scale := 1
    equation := by
      funext x
      simpa only [Tensor.reindex,Tensor.tensor,Units.val_one,one_mul] using congrFun hab x }⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
