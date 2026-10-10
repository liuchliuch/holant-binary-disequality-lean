import Holant.OpenNetworkComposition.Finite

/-! Literal boundary orders after deleting a free/free wire at a selected port. -/
namespace Holant.OpenNetworkComposition.ProjectiveContraction
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def tailBoundary : Fin n ↪ Fin (n+2) where
  toFun k := k.succ.succ
  inj' := by intro a b h; simpa using h

@[simp] theorem tailBoundary_apply (k : Fin n) : tailBoundary k=k.succ.succ := rfl

theorem tailBoundary_range (k : Fin (n+2)) :
    (∃l,tailBoundary l=k) ↔ k≠0 ∧ k≠1 := by
  constructor
  · rintro ⟨l,rfl⟩
    constructor <;> intro h <;> have hh := congrArg Fin.val h <;> simp [tailBoundary_apply] at hh
  · rintro ⟨h0,h1⟩
    have hk0 : k.val≠0 := fun h => h0 (Fin.ext (by simpa using h))
    have hk1 : k.val≠1 := fun h => h1 (Fin.ext (by simpa using h))
    refine ⟨⟨k.val-2,by omega⟩,?_⟩
    apply Fin.ext
    simp [tailBoundary_apply]
    omega

/-- After closing old0 to old1, a wire from old0 to old(q+2) transfers
old1 to output q; every other old surviving boundary keeps its order. -/
def moveFirstBoundary (q : Fin n) : Fin n ↪ Fin (n+2) where
  toFun k := if k=q then 1 else k.succ.succ
  inj' := by
    intro a b h
    by_cases ha : a=q <;> by_cases hb : b=q
    · exact ha.trans hb.symm
    · simp only [ha,hb,ite_true,ite_false] at h
      have hh := congrArg Fin.val h
      simp at hh
    · simp only [ha,hb,ite_true,ite_false] at h
      have hh := congrArg Fin.val h
      simp at hh
    · simp only [ha,hb,ite_false] at h
      simpa using h

@[simp] theorem moveFirstBoundary_apply (q k : Fin n) :
    moveFirstBoundary q k=(if k=q then 1 else k.succ.succ) := rfl

theorem moveFirstBoundary_range (q : Fin n) (k : Fin (n+2)) :
    (∃l,moveFirstBoundary q l=k) ↔ k≠0 ∧ k≠q.succ.succ := by
  constructor
  · rintro ⟨l,rfl⟩
    by_cases hl : l=q
    · simp [moveFirstBoundary_apply,hl,Fin.ext_iff]
    · simp only [moveFirstBoundary_apply,hl,ite_false]
      constructor
      · intro h; have := congrArg Fin.val h; simp at this
      · intro h; exact hl (by simpa using h)
  · rintro ⟨h0,hq⟩
    by_cases h1 : k=1
    · exact ⟨q,by simp [moveFirstBoundary_apply,h1]⟩
    · obtain ⟨l,hl⟩ := (tailBoundary_range k).mpr ⟨h0,h1⟩
      have hlq : l≠q := by intro h; subst l; exact hq hl.symm
      exact ⟨l,by simpa [moveFirstBoundary_apply,hlq,tailBoundary_apply] using hl⟩

def moveSecondBoundary (q : Fin n) : Fin n ↪ Fin (n+2) where
  toFun k := if k=q then 0 else k.succ.succ
  inj' := by
    intro a b h
    by_cases ha : a=q <;> by_cases hb : b=q
    · exact ha.trans hb.symm
    · simp only [ha,hb,ite_true,ite_false] at h
      have hh := congrArg Fin.val h
      simp at hh
    · simp only [ha,hb,ite_true,ite_false] at h
      have hh := congrArg Fin.val h
      simp at hh
    · simp only [ha,hb,ite_false] at h
      simpa using h

@[simp] theorem moveSecondBoundary_apply (q k : Fin n) :
    moveSecondBoundary q k=(if k=q then 0 else k.succ.succ) := rfl

theorem moveSecondBoundary_range (q : Fin n) (k : Fin (n+2)) :
    (∃l,moveSecondBoundary q l=k) ↔ k≠1 ∧ k≠q.succ.succ := by
  constructor
  · rintro ⟨l,rfl⟩
    by_cases hl : l=q
    · simp [moveSecondBoundary_apply,hl,Fin.ext_iff]
    · simp only [moveSecondBoundary_apply,hl,ite_false]
      constructor
      · intro h; have := congrArg Fin.val h; simp at this
      · intro h; exact hl (by simpa using h)
  · rintro ⟨h1,hq⟩
    by_cases h0 : k=0
    · exact ⟨q,by simp [moveSecondBoundary_apply,h0]⟩
    · obtain ⟨l,hl⟩ := (tailBoundary_range k).mpr ⟨h0,h1⟩
      have hlq : l≠q := by intro h; subst l; exact hq hl.symm
      exact ⟨l,by simpa [moveSecondBoundary_apply,hlq,tailBoundary_apply] using hl⟩

theorem tailBoundary_fill (a b : Bool) (x : Fin n → Bool) :
    (fun k => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) (tailBoundary k))=x := rfl

theorem moveFirstBoundary_fill (q : Fin n) (a : Bool) (x : Fin n → Bool) :
    (fun k => (Fin.cons a (Fin.cons (x q) x) : Fin (n+2) → Bool) (moveFirstBoundary q k))=x := by
  funext k
  by_cases hk : k=q <;> simp [moveFirstBoundary_apply,hk]

theorem moveSecondBoundary_fill (q : Fin n) (b : Bool) (x : Fin n → Bool) :
    (fun k => (Fin.cons (x q) (Fin.cons b x) : Fin (n+2) → Bool) (moveSecondBoundary q k))=x := by
  funext k
  by_cases hk : k=q <;> simp [moveSecondBoundary_apply,hk]

end Holant.OpenNetworkComposition.ProjectiveContraction
