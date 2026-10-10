import Holant.Complexity.FixedGadgetSubstitution.TemplateFamily
import Holant.Complexity.FixedGadgetSubstitution.Identity

/-! Adjoining one fixed ordinary gadget preserves the original finite labels,
ordered ports, coefficient field and oracle answer encoding. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Adjoin
open Computability Holant.Algebraic
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity)
variable (g : Template) (hg : g.WellFormed s b arity)

def templates (s : ℕ) (arity : ℕ → ℕ) (g : Template) (i : ℕ) : Template :=
  if i<s then identityTemplate arity i else g

include hg in
theorem wellFormed : ∀i < s+1,(templates s arity g i).WellFormed s b arity := by
  intro i hi
  by_cases h : i<s
  · simpa only [templates,if_pos h] using
      identityTemplate_wellFormed (b:=b) arity (⟨i,h⟩ : Fin s)
  · simpa only [templates,if_neg h] using hg

@[simp] theorem old_boundary (i : Fin s) :
    sourceArity (templates s arity g) i.val = arity i.val := by
  simp [sourceArity,templates,i.isLt,identityTemplate]

@[simp] theorem new_boundary :
    sourceArity (templates s arity g) s = g.boundary := by
  simp [sourceArity,templates]

def coordinates : (i : Fin (s+1)) → Signature (Fin n → ℚ)
    (sourceArity (templates s arity g) i.val) :=
  templateCoordinates F (templates s arity g) (wellFormed g hg) T

def macroCoordinates (g : Template) (hg : g.WellFormed s b arity) :
    Signature (Fin n → ℚ) g.boundary := fun x => F.decode.symm
  ((g.network hg (fun j y => F.decode (T.vertex j y))
    (fun j a b => F.decode (T.edge j a b))).denote x)

theorem macroCoordinates_congr {g₁ g₂ : Template}
    (h₁ : g₁.WellFormed s b arity) (h₂ : g₂.WellFormed s b arity)
    (he : g₁=g₂) : HEq (macroCoordinates F T g₁ h₁) (macroCoordinates F T g₂ h₂) := by
  cases he
  rfl

/-- Every old label is literally preserved, including all coefficient coordinates. -/
theorem old_coordinates (i : Fin s) :
    HEq (coordinates F T g hg ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩)
      (T.vertex i) := by
  change HEq (macroCoordinates F T (templates s arity g i.val) _) (T.vertex i)
  apply HEq.trans (macroCoordinates_congr F T _
    (identityTemplate_wellFormed (b:=b) arity i)
    (show templates s arity g i.val=identityTemplate arity i.val by simp [templates,i.isLt]))
  apply heq_of_eq
  funext x
  apply F.decode.injective
  rw [macroCoordinates,LinearEquiv.apply_symm_apply]
  exact congrFun (identityTemplate_denote arity i
    (fun j y => F.decode (T.vertex j y))
    (fun j a b => F.decode (T.edge j a b))) x

/-- The new label denotes the exact physical macro, with no implicit projective scalar. -/
theorem new_coordinates :
    HEq (coordinates F T g hg ⟨s,Nat.lt_succ_self s⟩)
      (fun x => F.decode.symm ((g.network hg
        (fun j y => F.decode (T.vertex j y))
        (fun j a b => F.decode (T.edge j a b))).denote x)) := by
  change HEq (macroCoordinates F T (templates s arity g s) _) (macroCoordinates F T g hg)
  exact macroCoordinates_congr F T _ hg (by simp [templates])

/-- One original fixed family plus the one actual macro reduces by an explicit
polynomial Boolean machine to the original family over the same faithful codec. -/
def reduction : PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) b (sourceArity (templates s arity g))) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((sourceTables (templates s arity g) T (coordinates F T g hg)).evaluate F)
    (T.evaluate F) :=
  templateFamilyReduction F (templates s arity g) (wellFormed g hg) T

 theorem reducible : OracleReducible
    (RawClosedNetwork.validatedEncoding (s+1) b (sourceArity (templates s arity g))) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((sourceTables (templates s arity g) T (coordinates F T g hg)).evaluate F)
    (T.evaluate F) := ⟨reduction F T g hg⟩

end
end Holant.Complexity.FixedGadgetSubstitution.Adjoin
