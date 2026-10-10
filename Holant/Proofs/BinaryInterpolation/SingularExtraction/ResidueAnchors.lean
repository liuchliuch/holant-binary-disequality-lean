import Holant.Proofs.BinaryInterpolation.SingularExtraction.RawDisjoint


noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueAnchors
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork RawGrouping RawDisjoint

variable {K : Type*} [Field K] {s b : ℕ} {arity : ℕ → ℕ}
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {r : RawClosedNetwork // r.WellFormed s b arity}

def empty : Input s b arity := ⟨⟨[], []⟩, by
  apply (wellFormed_iff_members _ _ _ _).mpr
  simp [RawClosedNetwork.endpoints, RawClosedNetwork.expectedEndpoints]⟩

def value (F : Choice.Table K) (r : Input s b arity) : K :=
  Choice.evaluate F r.val.edges.length r.val.vertices

def residue (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l) (r : Input s b arity) : Fin k × Fin l :=
  (⟨occurrences a r.val % k, Nat.mod_lt _ hk⟩,
   ⟨occurrences c r.val % l, Nat.mod_lt _ hl⟩)

def Live (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : Fin k × Fin l) : Prop :=
  ∃ r : Input s b arity, residue a c k l hk hl r = ρ ∧ value F r ≠ 0

def witness (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : Fin k × Fin l) : Input s b arity :=
  if h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl ρ then Classical.choose h else empty

theorem witness_spec (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : Fin k × Fin l) (h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl ρ) :
    residue a c k l hk hl (witness F a c k l hk hl ρ : Input s b arity) = ρ ∧
      value F (witness F a c k l hk hl ρ : Input s b arity) ≠ 0 := by
  simpa only [witness, dif_pos h] using Classical.choose_spec h

theorem dead_value (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (r : Input s b arity)
    (h : ¬ Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) : value F r = 0 := by
  by_contra hn
  exact h ⟨r, rfl, hn⟩

def anchor (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : Fin k × Fin l) : Input s b arity :=
  let w : Input s b arity := witness F a c k l hk hl ρ
  ⟨copies w.val (k*l-1), copies_wellFormed w.property _⟩

theorem anchor_value (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : Fin k × Fin l) :
    value F (anchor F a c k l hk hl ρ : Input s b arity) =
      value F (witness F a c k l hk hl ρ : Input s b arity) ^ (k*l-1) :=
  copies_value F _ (witness F a c k l hk hl ρ : Input s b arity).property _

theorem anchor_nonzero (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : Fin k × Fin l) (h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl ρ) :
    value F (anchor F a c k l hk hl ρ : Input s b arity) ≠ 0 := by
  rw [anchor_value]
  exact pow_ne_zero _ (witness_spec F a c k l hk hl ρ h).2

def augmented (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (r : Input s b arity) : Input s b arity :=
  let t := anchor F a c k l hk hl (residue a c k l hk hl r)
  ⟨union r.val t.val, union_wellFormed r.property t.property⟩

theorem augmented_value (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (r : Input s b arity) :
    value F (augmented F a c k l hk hl r) =
      value F r * value F (anchor F a c k l hk hl (residue a c k l hk hl r) : Input s b arity) :=
  union_value F _ _ (bounded_of_wellFormed _ r.property)
    (bounded_of_wellFormed _ (anchor F a c k l hk hl (residue a c k l hk hl r) : Input s b arity).property)

theorem complete_mod (d R m w : ℕ) (hR : 0 < R) (hdR : d ∣ R)
    (h : m % d = w % d) : d ∣ m + (R-1)*w := by
  apply Nat.dvd_of_mod_eq_zero
  calc
    (m + (R-1)*w) % d = (w + (R-1)*w) % d := by
      calc
        _ = (m%d + ((R-1)*w)%d)%d := Nat.add_mod _ _ _
        _ = (w%d + ((R-1)*w)%d)%d := congrArg (fun z => (z + ((R-1)*w)%d)%d) h
        _ = _ := (Nat.add_mod _ _ _).symm
    _ = (R*w) % d := by
      congr 1
      calc
        w + (R-1)*w = ((R-1)+1)*w := by ring
        _ = R*w := by rw [Nat.sub_add_cancel (by omega)]
    _ = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdR w)

/-- Independent divisibility of both actual augmented counts. -/
theorem augmented_counts (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (r : Input s b arity) (h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) :
    k ∣ occurrences a (augmented F a c k l hk hl r).val ∧
    l ∣ occurrences c (augmented F a c k l hk hl r).val := by
  have hw := (witness_spec F a c k l hk hl (residue a c k l hk hl r) h).1
  have h₁ := congrArg (fun z : Fin k × Fin l => z.1.val) hw
  have h₂ := congrArg (fun z : Fin k × Fin l => z.2.val) hw
  dsimp only [residue] at h₁ h₂
  dsimp only [augmented, anchor]
  rw [occurrences_union, occurrences_copies, occurrences_union, occurrences_copies]
  exact ⟨complete_mod k (k*l) _ _ (Nat.mul_pos hk hl) (dvd_mul_right k l) h₁.symm,
    complete_mod l (k*l) _ _ (Nat.mul_pos hk hl) (dvd_mul_left l k) h₂.symm⟩

/-- One oracle answer from the augmented graph recovers the original value.
Only a fixed class-dependent nonzero scalar is inverted. -/
theorem recover_live (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (r : Input s b arity) (h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) :
    value F (augmented F a c k l hk hl r) /
        value F (anchor F a c k l hk hl (residue a c k l hk hl r) : Input s b arity) =
      value F r := by
  rw [augmented_value]
  exact mul_div_cancel_right₀ _ (anchor_nonzero F a c k l hk hl _ h)

/-- A finite table is fixed before the input. Its size is a family constant. -/
def anchorSize (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l) : ℕ :=
  Finset.univ.sup fun ρ : Fin k × Fin l =>
    let t : Input s b arity := anchor F a c k l hk hl ρ
    t.val.vertices.length + t.val.edges.length

theorem augmented_size (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (r : Input s b arity) :
    (augmented F a c k l hk hl r).val.vertices.length +
        (augmented F a c k l hk hl r).val.edges.length ≤
      (RawClosedNetwork.encoding.encode r.val).length +
        anchorSize (s:=s) (b:=b) (arity:=arity) F a c k l hk hl := by
  have hi := r.val.counts_le_encoded_length
  have ht :
      let t : Input s b arity := anchor F a c k l hk hl (residue a c k l hk hl r)
      t.val.vertices.length + t.val.edges.length ≤
        anchorSize (s:=s) (b:=b) (arity:=arity) F a c k l hk hl :=
    Finset.le_sup (f := fun ρ : Fin k × Fin l =>
      let t : Input s b arity := anchor F a c k l hk hl ρ
      t.val.vertices.length + t.val.edges.length) (Finset.mem_univ _)
  dsimp only [augmented]
  rw [union_vertices, union_edges]
  omega

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueAnchors
