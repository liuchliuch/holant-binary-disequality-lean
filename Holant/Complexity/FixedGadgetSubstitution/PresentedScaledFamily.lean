import Holant.Complexity.FixedGadgetSubstitution.ProjectiveOriginalFamily

/-! A derived finite common field may contain fixed algebraic normalization
constants without adding any signature to the target family. The coefficient
index is distinct from the vertex-label index throughout. -/
namespace Holant.Complexity.FixedGadgetSubstitution.PresentedScaledFamily
open Computability Holant.Algebraic ExactSignatureTables
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {L J : Type} [Field L] [Algebra ℚ L] [Fintype J]
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (values : J → L) (halg : ∀j,IsAlgebraic ℚ (values j))
variable (lookup : CoefficientIndex s b arity → J)

def tables : ExactSignatureTables (Module.finrank ℚ (familyField values)) s b arity where
  vertex i x := familyCoordinates values halg (lookup (.inl ⟨i,x⟩))
  edge i a b := familyCoordinates values halg (lookup (.inr (i,a,b)))

variable (g : Template) (hg : g.WellFormed s b arity)

theorem macro_value_exact (x : Fin g.boundary → Bool) :
    (((g.network hg
      (fun i x => (familyPresentation values halg).decode ((tables values halg lookup).vertex i x))
      (fun i a b => (familyPresentation values halg).decode ((tables values halg lookup).edge i a b))).denote x
      : familyField values) : L) =
    (OriginalFamily.ambientMacro (fun a => values (lookup a)) g hg).denote x := by
  have hm : (g.network hg
      (fun i x => (familyPresentation values halg).decode ((tables values halg lookup).vertex i x))
      (fun i a b => (familyPresentation values halg).decode ((tables values halg lookup).edge i a b))).map
      (familyField values).subtype = OriginalFamily.ambientMacro (fun a => values (lookup a)) g hg := by
    unfold Network.map Template.network OriginalFamily.ambientMacro tables
    congr 1
    · funext v y
      exact familyCoordinates_spec values halg _
    · funext e a b
      exact familyCoordinates_spec values halg _
  rw [←hm]
  exact (Network.denote_map (familyField values).subtype _ x).symm

variable (scale : familyField values)

def ambientSource (i : Fin (s+1)) :
    Signature L (sourceArity (Adjoin.templates s arity g) i.val) := fun x =>
  OriginalFamily.ambientSource (fun a => values (lookup a)) g hg i x /
    (if i.val=s then (scale:L) else 1)

theorem ambientSource_old (i : Fin s) :
    HEq (ambientSource values lookup g hg scale
      ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩)
      (fun x => values (lookup (.inl ⟨i,x⟩))) := by
  unfold ambientSource
  simp only [Nat.ne_of_lt i.isLt,ite_false,div_one]
  exact OriginalFamily.ambientSource_old (fun a => values (lookup a)) g hg i

theorem ambientSource_new :
    HEq (ambientSource values lookup g hg scale ⟨s,Nat.lt_succ_self s⟩)
      (fun x => (OriginalFamily.ambientMacro (fun a => values (lookup a)) g hg).denote x/(scale:L)) := by
  unfold ambientSource
  simp only [ite_true]
  exact ProjectiveOriginalFamily.divide_heq _ _ (Adjoin.new_boundary g)
    (OriginalFamily.ambientSource_new (fun a => values (lookup a)) g hg) _

theorem ambientSource_family :
    Set.range (fun i : Fin (s+1) => (⟨sourceArity (Adjoin.templates s arity g) i.val,
      ambientSource values lookup g hg scale i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s => (⟨arity i.val,fun x => values (lookup (.inl ⟨i,x⟩))⟩ : AnySignature L)) ∪
      {⟨g.boundary,fun x => (OriginalFamily.ambientMacro (fun a => values (lookup a)) g hg).denote x/(scale:L)⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases h : i.val<s
    · left
      refine ⟨⟨i.val,h⟩,?_⟩
      exact (Sigma.ext (Adjoin.old_boundary g ⟨i.val,h⟩)
        (ambientSource_old values lookup g hg scale ⟨i.val,h⟩)).symm
    · right
      have hi : i.val=s := by omega
      have he : i=⟨s,Nat.lt_succ_self s⟩ := Fin.ext hi
      subst i
      exact Sigma.ext (Adjoin.new_boundary g) (ambientSource_new values lookup g hg scale)
  · intro h
    rcases h with ⟨i,rfl⟩ | h
    · refine ⟨⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩,?_⟩
      exact Sigma.ext (Adjoin.old_boundary g i) (ambientSource_old values lookup g hg scale i)
    · change f=⟨g.boundary,fun x =>
        (OriginalFamily.ambientMacro (fun a => values (lookup a)) g hg).denote x/(scale:L)⟩ at h
      subst f
      exact ⟨⟨s,Nat.lt_succ_self s⟩,
        Sigma.ext (Adjoin.new_boundary g) (ambientSource_new values lookup g hg scale)⟩

theorem coordinates_value_exact (i : Fin (s+1))
    (x : Fin (sourceArity (Adjoin.templates s arity g) i.val) → Bool) :
    (((familyPresentation values halg).decode
      (ScaledAdjoin.coordinates (familyPresentation values halg)
        (tables values halg lookup) g hg scale i x) : familyField values) : L) =
      ambientSource values lookup g hg scale i x := by
  unfold ScaledAdjoin.coordinates ScaledAdjoin.rescale
  rw [LinearEquiv.apply_symm_apply,Subfield.coe_div]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates,macro_value_exact]
  unfold ambientSource OriginalFamily.ambientSource
  split_ifs <;> rfl

theorem source_value_exact
    (r : Input (s+1) b (sourceArity (Adjoin.templates s arity g))) :
    (((sourceTables (Adjoin.templates s arity g) (tables values halg lookup)
      (ScaledAdjoin.coordinates (familyPresentation values halg)
        (tables values halg lookup) g hg scale)).evaluate
      (familyPresentation values halg) r : familyField values) : L) =
    (r.val.realize r.property (ambientSource values lookup g hg scale)
      (fun i a b => values (lookup (.inr (i,a,b))))).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (familyField values).subtype _ = _
  rw [←Network.denote_map (familyField values).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact coordinates_value_exact values halg lookup g hg scale
      (RawClosedNetwork.signatureLabel r.property v) x
  · funext e a b
    exact familyCoordinates_spec values halg _

theorem target_value_exact (r : Input s b arity) :
    (((tables values halg lookup).evaluate (familyPresentation values halg) r : familyField values) : L) =
    (r.val.realize r.property (fun i x => values (lookup (.inl ⟨i,x⟩)))
      (fun i a b => values (lookup (.inr (i,a,b))))).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (familyField values).subtype _ = _
  rw [←Network.denote_map (familyField values).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact familyCoordinates_spec values halg _
  · funext e a b
    exact familyCoordinates_spec values halg _

abbrev ReductionType := PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) b
      (sourceArity (Adjoin.templates s arity g)))
    (familyPresentation values halg).encoding
    (RawClosedNetwork.validatedEncoding s b arity)
    (familyPresentation values halg).encoding
    ((sourceTables (Adjoin.templates s arity g) (tables values halg lookup)
      (ScaledAdjoin.coordinates (familyPresentation values halg)
        (tables values halg lookup) g hg scale)).evaluate
      (familyPresentation values halg))
    ((tables values halg lookup).evaluate (familyPresentation values halg))

def reduction (hscale : scale≠0) : ReductionType values halg lookup g hg scale :=
  ScaledAdjoin.reduction (familyPresentation values halg)
    (tables values halg lookup) g hg scale hscale
end
end Holant.Complexity.FixedGadgetSubstitution.PresentedScaledFamily
