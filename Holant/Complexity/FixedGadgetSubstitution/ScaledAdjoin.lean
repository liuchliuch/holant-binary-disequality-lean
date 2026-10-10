import Holant.Complexity.FixedGadgetSubstitution.Adjoin

/-! Adjoining a fixed projective macro with its nonzero field scalar recorded.
The reduction uses the existing actual occurrence-count correction machine. -/
namespace Holant.Complexity.FixedGadgetSubstitution.ScaledAdjoin
open Holant.Algebraic Computability
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity)
variable (g : Template) (hg : g.WellFormed s b arity) (scale : K)

def rescale {m : ℕ} (f : Signature (Fin n → ℚ) m) : Signature (Fin n → ℚ) m :=
  fun x => F.decode.symm (F.decode (f x)/scale)

def coordinates (i : Fin (s+1)) :
    Signature (Fin n → ℚ) (sourceArity (Adjoin.templates s arity g) i.val) :=
  rescale F (if i.val=s then scale else 1) (Adjoin.coordinates F T g hg i)

 theorem rescale_one {m : ℕ} (f : Signature (Fin n → ℚ) m) : rescale F 1 f=f := by
  funext x
  simp only [rescale,div_one,LinearEquiv.symm_apply_apply]

 theorem rescale_congr {m k : ℕ} (f : Signature (Fin n → ℚ) m)
    (h : Signature (Fin n → ℚ) k) (hm : m = k) (he : HEq f h) : HEq (rescale F scale f) (rescale F scale h) := by
  subst k
  cases eq_of_heq he
  rfl

 theorem old_coordinates (i : Fin s) :
    HEq (coordinates F T g hg scale ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩) (T.vertex i) := by
  have hi : i.val≠s := Nat.ne_of_lt i.isLt
  unfold coordinates
  simp only [hi,ite_false,rescale_one]
  exact Adjoin.old_coordinates F T g hg i

 theorem new_coordinates :
    HEq (coordinates F T g hg scale ⟨s,Nat.lt_succ_self s⟩)
      (fun x => F.decode.symm (((g.network hg
        (fun j y => F.decode (T.vertex j y))
        (fun j a b => F.decode (T.edge j a b))).denote x)/scale)) := by
  unfold coordinates
  simp only [ite_true]
  apply HEq.trans (rescale_congr F scale _ _ (Adjoin.new_boundary g)
    (Adjoin.new_coordinates F T g hg))
  apply heq_of_eq
  funext x
  simp only [rescale,LinearEquiv.apply_symm_apply]

/-- Every original occurrence receives scale1; only the appended signature
receives the one recorded nonzero multiplier. -/
def reduction (hscale : scale≠0) : PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) b (sourceArity (Adjoin.templates s arity g))) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((sourceTables (Adjoin.templates s arity g) T (coordinates F T g hg scale)).evaluate F)
    (T.evaluate F) := by
  apply FixedGadgetSubstitution.reduction F (Adjoin.templates s arity g)
    (Adjoin.wellFormed g hg) T (coordinates F T g hg scale) s scale hscale
  intro i
  funext x
  change ((Adjoin.templates s arity g i.val).network _
    (fun j y => F.decode (T.vertex j y)) (fun j a b => F.decode (T.edge j a b))).denote x =
      (if i.val=s then scale else 1)*F.decode (coordinates F T g hg scale i x)
  unfold coordinates rescale
  rw [LinearEquiv.apply_symm_apply]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates]
  have hn : (if i.val=s then scale else 1)≠0 := by split_ifs <;> simp_all
  field_simp

end
end Holant.Complexity.FixedGadgetSubstitution.ScaledAdjoin
