import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily
import Holant.Complexity.FixedGadgetSubstitution.ScaledAdjoin

/-! Fixed projective macros over the field of the original finite family.
The scale is a field element, not an extra oracle input. A nonzero known pivot
recovers this element directly from the literal macro coefficient. -/
namespace Holant.Complexity.FixedGadgetSubstitution.ProjectiveOriginalFamily
open Computability Holant.Algebraic ExactSignatureTables
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {L : Type} [Field L] [Algebra ℚ L] {s b : ℕ} {arity : ℕ → ℕ}
variable (coeff : CoefficientIndex s b arity → L)
variable (halg : ∀a, IsAlgebraic ℚ (coeff a))
variable (g : Template) (hg : g.WellFormed s b arity)
variable (scale : familyField coeff)

def ambientSource (i : Fin (s+1)) :
    Signature L (sourceArity (Adjoin.templates s arity g) i.val) :=
  fun x => OriginalFamily.ambientSource coeff g hg i x /
    (if i.val=s then (scale : L) else 1)

theorem ambientSource_old (i : Fin s) :
    HEq (ambientSource coeff g hg scale
      ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩)
      (fun x => coeff (.inl ⟨i,x⟩)) := by
  have hi : i.val≠s := Nat.ne_of_lt i.isLt
  unfold ambientSource
  simp only [hi,ite_false,div_one]
  exact OriginalFamily.ambientSource_old coeff g hg i

theorem divide_heq {m k : ℕ} (f : Signature L m) (h : Signature L k)
    (hm : m=k) (he : HEq f h) (c : L) :
    HEq (fun x => f x/c) (fun x => h x/c) := by
  subst k
  cases eq_of_heq he
  rfl

theorem ambientSource_new :
    HEq (ambientSource coeff g hg scale ⟨s,Nat.lt_succ_self s⟩)
      (fun x => (OriginalFamily.ambientMacro coeff g hg).denote x/(scale:L)) := by
  unfold ambientSource
  simp only [ite_true]
  exact divide_heq _ _ (Adjoin.new_boundary g)
    (OriginalFamily.ambientSource_new coeff g hg) _

theorem ambientSource_family :
    Set.range (fun i : Fin (s+1) => (⟨sourceArity (Adjoin.templates s arity g) i.val,
      ambientSource coeff g hg scale i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s => (⟨arity i.val,fun x => coeff (.inl ⟨i,x⟩)⟩ : AnySignature L)) ∪
      {⟨g.boundary,fun x => (OriginalFamily.ambientMacro coeff g hg).denote x/(scale:L)⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases h : i.val<s
    · left
      refine ⟨⟨i.val,h⟩,?_⟩
      exact (Sigma.ext (Adjoin.old_boundary g ⟨i.val,h⟩)
        (ambientSource_old coeff g hg scale ⟨i.val,h⟩)).symm
    · right
      have hi : i.val=s := by omega
      have he : i=⟨s,Nat.lt_succ_self s⟩ := Fin.ext hi
      subst i
      exact Sigma.ext (Adjoin.new_boundary g) (ambientSource_new coeff g hg scale)
  · intro h
    rcases h with ⟨i,rfl⟩ | h
    · refine ⟨⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩,?_⟩
      exact Sigma.ext (Adjoin.old_boundary g i) (ambientSource_old coeff g hg scale i)
    · change f=⟨g.boundary,fun x => (OriginalFamily.ambientMacro coeff g hg).denote x/(scale:L)⟩ at h
      subst f
      exact ⟨⟨s,Nat.lt_succ_self s⟩,
        Sigma.ext (Adjoin.new_boundary g) (ambientSource_new coeff g hg scale)⟩

theorem coordinates_value_exact (i : Fin (s+1))
    (x : Fin (sourceArity (Adjoin.templates s arity g) i.val) → Bool) :
    (((familyPresentation coeff halg).decode
      (ScaledAdjoin.coordinates (familyPresentation coeff halg)
        (OriginalFamily.tables coeff halg) g hg scale i x) : familyField coeff) : L) =
      ambientSource coeff g hg scale i x := by
  unfold ScaledAdjoin.coordinates ScaledAdjoin.rescale
  rw [LinearEquiv.apply_symm_apply,Subfield.coe_div]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates,OriginalFamily.macro_value_exact]
  unfold ambientSource OriginalFamily.ambientSource
  split_ifs <;> rfl

theorem source_value_exact
    (r : ExactSignatureTables.Input (s+1) b (sourceArity (Adjoin.templates s arity g))) :
    (((sourceTables (Adjoin.templates s arity g) (OriginalFamily.tables coeff halg)
      (ScaledAdjoin.coordinates (familyPresentation coeff halg)
        (OriginalFamily.tables coeff halg) g hg scale)).evaluate
        (familyPresentation coeff halg) r : familyField coeff) : L) =
      (r.val.realize r.property (ambientSource coeff g hg scale)
        (fun i a b => coeff (.inr (i,a,b)))).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (familyField coeff).subtype _ = _
  rw [←Network.denote_map (familyField coeff).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact coordinates_value_exact coeff halg g hg scale
      (RawClosedNetwork.signatureLabel r.property v) x
  · funext e a b
    exact familyCoordinates_spec coeff halg _

abbrev ReductionType := PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) b
      (sourceArity (Adjoin.templates s arity g)))
    (familyPresentation coeff halg).encoding
    (RawClosedNetwork.validatedEncoding s b arity)
    (familyPresentation coeff halg).encoding
    ((sourceTables (Adjoin.templates s arity g) (OriginalFamily.tables coeff halg)
      (ScaledAdjoin.coordinates (familyPresentation coeff halg)
        (OriginalFamily.tables coeff halg) g hg scale)).evaluate
        (familyPresentation coeff halg))
    ((OriginalFamily.tables coeff halg).evaluate (familyPresentation coeff halg))

def reduction (hscale : scale≠0) : ReductionType coeff halg g hg scale :=
  ScaledAdjoin.reduction (familyPresentation coeff halg)
    (OriginalFamily.tables coeff halg) g hg scale hscale

def pivotScale (p : Fin g.boundary → Bool) (pivot : familyField coeff) : familyField coeff :=
  (g.network hg
    (fun i x => (familyPresentation coeff halg).decode ((OriginalFamily.tables coeff halg).vertex i x))
    (fun i a b => (familyPresentation coeff halg).decode ((OriginalFamily.tables coeff halg).edge i a b))).denote p / pivot

theorem pivotScale_value (q : Signature L g.boundary) (c : L)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote = c • q)
    (p : Fin g.boundary → Bool) (pivot : familyField coeff)
    (hp : q p=(pivot:L)) (hn : pivot≠0) :
    (pivotScale coeff halg g hg p pivot : L)=c := by
  unfold pivotScale
  rw [Subfield.coe_div,OriginalFamily.macro_value_exact,hmacro]
  change c*q p/(pivot:L)=c
  rw [hp]
  have hn' : (pivot:L)≠0 := by exact_mod_cast hn
  exact mul_div_cancel_right₀ c hn'

theorem pivotScale_ne_zero (q : Signature L g.boundary) (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote = c • q)
    (p : Fin g.boundary → Bool) (pivot : familyField coeff)
    (hp : q p=(pivot:L)) (hn : pivot≠0) :
    pivotScale coeff halg g hg p pivot≠0 := by
  intro he
  have hv := pivotScale_value coeff halg g hg q c hmacro p pivot hp hn
  rw [he] at hv
  exact hc hv.symm

theorem pivot_normalized_macro (q : Signature L g.boundary) (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote = c • q)
    (p : Fin g.boundary → Bool) (pivot : familyField coeff)
    (hp : q p=(pivot:L)) (hn : pivot≠0) :
    (fun x => (OriginalFamily.ambientMacro coeff g hg).denote x /
      (pivotScale coeff halg g hg p pivot : L))=q := by
  funext x
  rw [pivotScale_value coeff halg g hg q c hmacro p pivot hp hn,hmacro]
  change c*q x/c=q x
  exact mul_div_cancel_left₀ (q x) hc
end
end Holant.Complexity.FixedGadgetSubstitution.ProjectiveOriginalFamily
