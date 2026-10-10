import Holant.Realization
import Holant.Complexity.FixedGadgetSubstitution.Adjoin
import Holant.Algebraic.FiniteFamilyNetwork

/-! The original finite algebraic coefficient family determines the field used
on both sides of fixed-gadget substitution. Macro coefficients stay in that
field by the literal network sum; no field representation is supplied as input. -/
namespace Holant.Complexity.FixedGadgetSubstitution.OriginalFamily
open Computability Holant.Algebraic ExactSignatureTables
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [Field L] [Algebra ℚ L] {s b : ℕ} {arity : ℕ → ℕ}
variable (coeff : CoefficientIndex s b arity → L)
variable (halg : ∀a,IsAlgebraic ℚ (coeff a))

def tables : ExactSignatureTables (Module.finrank ℚ (familyField coeff)) s b arity where
  vertex i x := familyCoordinates coeff halg (.inl ⟨i,x⟩)
  edge i a b := familyCoordinates coeff halg (.inr (i,a,b))

variable (g : Template) (hg : g.WellFormed s b arity)

def ambientMacro : Network L g.boundary :=
  g.network hg (fun i x => coeff (.inl ⟨i,x⟩)) (fun i a b => coeff (.inr (i,a,b)))

/-- Every original vertex value, edge value and ordered port is preserved. -/
theorem macro_map :
    (g.network hg
      (fun i x => (familyPresentation coeff halg).decode ((tables coeff halg).vertex i x))
      (fun i a b => (familyPresentation coeff halg).decode ((tables coeff halg).edge i a b))).map
      (familyField coeff).subtype = ambientMacro coeff g hg := by
  unfold Network.map Template.network ambientMacro tables
  congr 1
  · funext v x
    exact familyCoordinates_spec coeff halg _
  · funext e a b
    exact familyCoordinates_spec coeff halg _

 theorem macro_value_exact (x : Fin g.boundary → Bool) :
    (((g.network hg
      (fun i x => (familyPresentation coeff halg).decode ((tables coeff halg).vertex i x))
      (fun i a b => (familyPresentation coeff halg).decode ((tables coeff halg).edge i a b))).denote x
        : familyField coeff) : L) = (ambientMacro coeff g hg).denote x := by
  rw [←macro_map coeff halg g hg]
  exact (Network.denote_map (familyField coeff).subtype _ x).symm

def ambientSource (i : Fin (s+1)) :
    Signature L (sourceArity (Adjoin.templates s arity g) i.val) :=
  (ambientMacro coeff (Adjoin.templates s arity g i.val) (Adjoin.wellFormed g hg i.val i.isLt)).denote

theorem ambientMacro_congr {g₁ g₂ : Template}
    (h₁ : g₁.WellFormed s b arity) (h₂ : g₂.WellFormed s b arity)
    (he : g₁=g₂) : HEq (ambientMacro coeff g₁ h₁).denote (ambientMacro coeff g₂ h₂).denote := by
  cases he
  rfl

 theorem ambientSource_old (i : Fin s) :
    HEq (ambientSource coeff g hg ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩)
      (fun x => coeff (.inl ⟨i,x⟩)) := by
  apply HEq.trans (ambientMacro_congr coeff _
    (identityTemplate_wellFormed (b:=b) arity i)
    (show Adjoin.templates s arity g i.val=identityTemplate arity i.val by
      simp [Adjoin.templates,i.isLt]))
  exact heq_of_eq (identityTemplate_denote arity i
    (fun j x => coeff (.inl ⟨j,x⟩)) (fun j a b => coeff (.inr (j,a,b))))

 theorem ambientSource_new :
    HEq (ambientSource coeff g hg ⟨s,Nat.lt_succ_self s⟩) (ambientMacro coeff g hg).denote :=
  ambientMacro_congr coeff _ hg (by simp [Adjoin.templates])

/-- The represented source signature family is exactly the old family with the
one macro adjoined, including coincidences and an empty old family. -/
theorem ambientSource_family :
    Set.range (fun i : Fin (s+1) => (⟨sourceArity (Adjoin.templates s arity g) i.val,
      ambientSource coeff g hg i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s => (⟨arity i.val,fun x => coeff (.inl ⟨i,x⟩)⟩ : AnySignature L)) ∪
      {⟨g.boundary,(ambientMacro coeff g hg).denote⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases h : i.val<s
    · left
      refine ⟨⟨i.val,h⟩,?_⟩
      exact (Sigma.ext (Adjoin.old_boundary g ⟨i.val,h⟩)
        (ambientSource_old coeff g hg ⟨i.val,h⟩)).symm
    · right
      have hi : i.val=s := by omega
      have he : i=⟨s,Nat.lt_succ_self s⟩ := Fin.ext hi
      subst i
      exact Sigma.ext (Adjoin.new_boundary g) (ambientSource_new coeff g hg)
  · intro h
    rcases h with ⟨i,rfl⟩ | h
    · refine ⟨⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩,?_⟩
      exact Sigma.ext (Adjoin.old_boundary g i) (ambientSource_old coeff g hg i)
    · change f=⟨g.boundary,(ambientMacro coeff g hg).denote⟩ at h
      subst f
      exact ⟨⟨s,Nat.lt_succ_self s⟩,
        Sigma.ext (Adjoin.new_boundary g) (ambientSource_new coeff g hg)⟩

/-- The source function interprets precisely the original labels and newly
adjoined physical macro in the ambient field. -/
theorem source_value_exact
    (r : ExactSignatureTables.Input (s+1) b (sourceArity (Adjoin.templates s arity g))) :
    (((sourceTables (Adjoin.templates s arity g) (tables coeff halg)
      (Adjoin.coordinates (familyPresentation coeff halg) (tables coeff halg) g hg)).evaluate
        (familyPresentation coeff halg) r : familyField coeff) : L) =
      (r.val.realize r.property (ambientSource coeff g hg)
        (fun i a b => coeff (.inr (i,a,b)))).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (familyField coeff).subtype _ = _
  rw [←Network.denote_map (familyField coeff).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    dsimp only [sourceTables,Adjoin.coordinates]
    rw [decode_templateCoordinates]
    exact macro_value_exact coeff halg _ _ x
  · funext e a b
    exact familyCoordinates_spec coeff halg _

 theorem target_value_exact (r : ExactSignatureTables.Input s b arity) :
    (((tables coeff halg).evaluate (familyPresentation coeff halg) r : familyField coeff) : L) =
      (r.val.realize r.property (fun i x => coeff (.inl ⟨i,x⟩))
        (fun i a b => coeff (.inr (i,a,b)))).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (familyField coeff).subtype _ = _
  rw [←Network.denote_map (familyField coeff).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact familyCoordinates_spec coeff halg _
  · funext e a b
    exact familyCoordinates_spec coeff halg _

/-- Fixed-family reduction with a common field derived from the original
algebraic entries. The newly adjoined signature is exactly the actual macro. -/
abbrev ReductionType := PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) b
      (sourceArity (Adjoin.templates s arity g)))
    (familyPresentation coeff halg).encoding
    (RawClosedNetwork.validatedEncoding s b arity)
    (familyPresentation coeff halg).encoding
    ((sourceTables (Adjoin.templates s arity g) (tables coeff halg)
      (Adjoin.coordinates (familyPresentation coeff halg) (tables coeff halg) g hg)).evaluate
        (familyPresentation coeff halg))
    ((tables coeff halg).evaluate (familyPresentation coeff halg))

def reduction : ReductionType coeff halg g hg :=
  Adjoin.reduction (familyPresentation coeff halg) (tables coeff halg) g hg

 theorem reducible : OracleReducible
    (RawClosedNetwork.validatedEncoding (s+1) b
      (sourceArity (Adjoin.templates s arity g)))
    (familyPresentation coeff halg).encoding
    (RawClosedNetwork.validatedEncoding s b arity)
    (familyPresentation coeff halg).encoding
    ((sourceTables (Adjoin.templates s arity g) (tables coeff halg)
      (Adjoin.coordinates (familyPresentation coeff halg) (tables coeff halg) g hg)).evaluate
        (familyPresentation coeff halg))
    ((tables coeff halg).evaluate (familyPresentation coeff halg)) :=
  ⟨reduction coeff halg g hg⟩
end
end Holant.Complexity.FixedGadgetSubstitution.OriginalFamily
