import Holant.Dihedral.SixPortBase.Source

/-! The source deck contains the thirty ordered pairs, with the remaining
ports in their canonical increasing order. Arbitrary residual permutations
are derived by literal reindexing; no extra card premise is required. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Certificates.NormalizedDihedralQ6
set_option backward.isDefEq.respectTransparency false

 abbrev OrderedPair := {p : Pair // p.1 ≠ p.2}

 def selectedPair (o : Equiv.Perm (Fin 6)) : OrderedPair :=
  ⟨(o 0,o 1),fun hh => (by decide : (0 : Fin 6) ≠ 1) (o.injective hh)⟩

 def remainingOrder (o : Equiv.Perm (Fin 6)) : Fin 4 ≃ Remaining (selectedPair o).val :=
  Equiv.ofBijective (fun i => ⟨o i.succ.succ,by
    constructor
    · intro hh
      have he := o.injective hh
      have := congrArg Fin.val he
      simp only [Fin.val_succ,Fin.val_zero] at this
      omega
    · intro hh
      have he := o.injective hh
      have := congrArg Fin.val he
      simp only [Fin.val_succ,Fin.val_one] at this
      omega⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j hij
      have he := o.injective (congrArg Subtype.val hij)
      apply Fin.ext
      have hh := congrArg Fin.val he
      simpa using hh,by
      rw [Fintype.card_fin,remaining_card _ (selectedPair o).property]⟩)

 def canonicalResidual (o : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 4) :=
  (remainingOrder o).trans (remainingEquiv (selectedPair o).val (selectedPair o).property).symm

 theorem original_order_decomposition (o : Equiv.Perm (Fin 6)) :
    o=(liftPair (canonicalResidual o)).trans (orderedPorts (selectedPair o).val (selectedPair o).property) := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · rfl
  · rfl
  · change o k.succ.succ=(remainingEquiv (selectedPair o).val (selectedPair o).property
      ((remainingEquiv (selectedPair o).val (selectedPair o).property).symm (remainingOrder o k))).val
    rw [Equiv.apply_symm_apply]
    rfl

 theorem close_reindex_residual (q : Signature Scalar 6) (r : Equiv.Perm (Fin 4)) (γ : Bool) (t : Scalar) :
    close γ t (Tensor.reindex (liftPair r).symm q)=Tensor.reindex r.symm (close γ t q) := by
  funext x
  simp only [close,Tensor.reindex]
  simp_rw [word_liftPair]

 theorem canonical_card_reindex (h : Signature Scalar 6) (o : Equiv.Perm (Fin 6)) (γ : Bool) (t : Scalar) :
    close γ t (Tensor.reindex o.symm h)=
      Tensor.reindex (canonicalResidual o).symm
        (close γ t (Tensor.reindex (orderedPorts (selectedPair o).val (selectedPair o).property).symm h)) := by
  have he := original_order_decomposition o
  conv_lhs => rw [he]
  rw [Equiv.symm_trans,←Tensor.reindex_trans,close_reindex_residual]

 theorem matchingSample_reindex {m : ℕ} {q : Signature Scalar 4} (hq : MatchingSample m 2 q)
    (o : Equiv.Perm (Fin 4)) : MatchingSample m 2 (Tensor.reindex o q) := by
  obtain ⟨p,A,κ,hA,hκ,hq⟩ := hq
  refine ⟨p.trans o,A,κ,hA,hκ,?_⟩
  rw [hq]
  rfl

 theorem all_cards_of_canonical {m : ℕ} (h : Signature Scalar 6)
    (hs : ∀ p : OrderedPair,∀ γ t,Roots m t →
      close γ t (Tensor.reindex (orderedPorts p.val p.property).symm h)=0 ∨
      MatchingSample m 2 (close γ t (Tensor.reindex (orderedPorts p.val p.property).symm h))) : AllCards m h := by
  intro o γ t ht
  rw [canonical_card_reindex]
  rcases hs (selectedPair o) γ t ht with hz|hq
  · left
    rw [hz]
    rfl
  · exact Or.inr (matchingSample_reindex hq _)

/-- Precisely thirty ordered physical deleted pairs. Residual port order is
not an additional hypothesis or an implicit without-loss-of-generality step. -/
 theorem orderedPair_card : Fintype.card OrderedPair=30 := by decide

/-- Full source statement using only the literal canonical oriented deck.
The actual representative binary and every nonzero recorded card multiplier
are retained. The factors are exact tensors on a proved original-port split. -/
 theorem source_canonical_six_port_base {m : ℕ} (hm : 3≤m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m) (h : Signature Scalar 6)
    (hn : h ≠ 0)
    (c : OrderedPair → Bool → {t : Scalar // Roots m t} → Scalar)
    (hc : ∀ p γ t,c p γ t ≠ 0)
    (hs : ∀ p γ t,
      c p γ t • nativeCardValue (Tensor.reindex (orderedPorts p.val p.property).symm h)
        ((G.connections (by omega)).binary γ t)=0 ∨
      MatchingSample m 2 (c p γ t • nativeCardValue
        (Tensor.reindex (orderedPorts p.val p.property).symm h)
        ((G.connections (by omega)).binary γ t))) : HasFactor h ∧ ¬TensorPrime h := by
  let D := G.connections (by omega : 0<m)
  have hd : AllCards m h := by
    apply all_cards_of_canonical h
    intro p γ t ht
    let z : {t : Scalar // Roots m t} := ⟨t,ht⟩
    have hnz : c p γ z*D.multiplier γ z ≠ 0 := mul_ne_zero (hc p γ z) (D.multiplier_ne_zero γ z)
    have he : c p γ z • nativeCardValue (Tensor.reindex (orderedPorts p.val p.property).symm h) (D.binary γ z)=
        (c p γ z*D.multiplier γ z) • close γ t (Tensor.reindex (orderedPorts p.val p.property).symm h) := by
      rw [D.normalization,actual_close,smul_smul]
    have hh := hs p γ z
    change c p γ z • nativeCardValue (Tensor.reindex (orderedPorts p.val p.property).symm h) (D.binary γ z)=0 ∨
      MatchingSample m 2 (c p γ z • nativeCardValue (Tensor.reindex (orderedPorts p.val p.property).symm h) (D.binary γ z)) at hh
    rw [he] at hh
    rcases hh with hz|hq
    · left
      by_contra hnon
      exact scalar_tensor_nonzero hnz hnon hz
    · exact Or.inr (SectorRuling.MatchingSample.of_scale _ hnz hq)
  exact ⟨source_six_port_base hm h hn hd,source_no_six_port_prime hm h hd⟩

end Holant.Dihedral.SixPortBase
