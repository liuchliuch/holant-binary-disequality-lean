import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineAlternatingOrbits

/-! Canonical coordinates for the actual alternating permutation orbits. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open Equiv
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

 def orbitSet (M N : Matching P r) (p : P) : Finset P := by
  classical
  exact Finset.univ.filter ((M.alternating N).SameCycle p)

@[simp] theorem mem_orbitSet (M N : Matching P r) (p q : P) :
    q ∈ M.orbitSet N p ↔ (M.alternating N).SameCycle p q := by
  classical
  simp [orbitSet]

 theorem self_mem_orbitSet (M N : Matching P r) (p : P) : p ∈ M.orbitSet N p :=
  (mem_orbitSet M N p p).mpr Equiv.Perm.SameCycle.rfl

 theorem orbitSet_nonempty (M N : Matching P r) (p : P) : (M.orbitSet N p).Nonempty :=
  ⟨p,M.self_mem_orbitSet N p⟩

 def orbitHead (M N : Matching P r) (p : P) : P :=
  (M.orbitSet N p).min' (M.orbitSet_nonempty N p)

 theorem sameCycle_head (M N : Matching P r) (p : P) :
    (M.alternating N).SameCycle p (M.orbitHead N p) :=
  (mem_orbitSet M N p _).mp (Finset.min'_mem _ _)

 theorem orbitSet_eq (M N : Matching P r) {p q : P}
    (h : (M.alternating N).SameCycle p q) : M.orbitSet N p = M.orbitSet N q := by
  ext x
  simp only [mem_orbitSet]
  exact ⟨fun hx => h.symm.trans hx,fun hx => h.trans hx⟩

 theorem orbitHead_eq_iff (M N : Matching P r) (p q : P) :
    M.orbitHead N p = M.orbitHead N q ↔ (M.alternating N).SameCycle p q := by
  constructor
  · intro h
    have hp := M.sameCycle_head N p
    rw [h] at hp
    exact hp.trans (M.sameCycle_head N q).symm
  · intro h
    unfold orbitHead
    congr 1
    exact M.orbitSet_eq N h

@[simp] theorem orbitHead_head (M N : Matching P r) (p : P) :
    M.orbitHead N (M.orbitHead N p) = M.orbitHead N p :=
  (M.orbitHead_eq_iff N _ _).mpr (M.sameCycle_head N p).symm

 theorem orbitHead_mate_head (M N : Matching P r) (p : P) :
    M.orbitHead N (M.mate (M.orbitHead N p)) = M.orbitHead N (M.mate p) :=
  (M.orbitHead_eq_iff N _ _).mpr ((M.sameCycle_mate_iff N _ _).mpr (M.sameCycle_head N p).symm)

 theorem orbitHead_ne_mate (M N : Matching P r) (p : P) :
    M.orbitHead N p ≠ M.orbitHead N (M.mate p) := by
  intro h
  exact M.mate_not_sameCycle N p ((M.orbitHead_eq_iff N _ _).mp h)

 theorem isCycleOn_orbitSet (M N : Matching P r) (p : P) :
    (M.alternating N).IsCycleOn (M.orbitSet N p) := by
  refine ⟨⟨?_,(M.alternating N).injective.injOn,?_⟩,?_⟩
  · intro q hq
    exact (mem_orbitSet M N p _).mpr ((mem_orbitSet M N p q).mp hq).apply_right
  · intro q hq
    refine ⟨(M.alternating N).symm q,?_,by simp⟩
    exact (mem_orbitSet M N p _).mpr ((mem_orbitSet M N p q).mp hq).symm_apply_right
  · intro q hq s hs
    exact ((mem_orbitSet M N p q).mp hq).symm.trans ((mem_orbitSet M N p s).mp hs)

 def orbitEquiv (M N : Matching P r) (p : P) :
    Fin (M.orbitSet N p).card ≃ {q // q ∈ M.orbitSet N p} :=
  Equiv.ofBijective
    (fun i => ⟨((M.alternating N)^i.val) p,
      (mem_orbitSet M N p _).mpr (Equiv.Perm.SameCycle.rfl.pow_right)⟩)
    (by
      constructor
      · intro i j h
        have hh := ((M.isCycleOn_orbitSet N p).pow_apply_eq_pow_apply
          (M.self_mem_orbitSet N p)).mp (congrArg Subtype.val h)
        apply Fin.ext
        change i.val % (M.orbitSet N p).card = j.val % (M.orbitSet N p).card at hh
        simpa only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hh
      · intro q
        obtain ⟨n,hn,he⟩ := (M.isCycleOn_orbitSet N p).exists_pow_eq
          (M.self_mem_orbitSet N p) q.property
        exact ⟨⟨n,hn⟩,Subtype.ext he⟩)

@[simp] theorem orbitEquiv_val (M N : Matching P r) (p : P)
    (i : Fin (M.orbitSet N p).card) :
    (M.orbitEquiv N p i).val = ((M.alternating N)^i.val) p := rfl

end Matching
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
