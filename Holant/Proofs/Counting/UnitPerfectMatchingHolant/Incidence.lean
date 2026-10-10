import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Tree
import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Network
import Mathlib.Algebra.BigOperators.Ring.Finset


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Incidence
open Holant
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation

abbrev Selection (g : UnitInput) := UnitEdges g → Bool
abbrev Nodes (g : UnitInput) := Fin g.val.1 ⊕ Fin g.val.1

/-- The two copies are distinct even when their numerical index agrees. -/
theorem row_ne_column (g : UnitInput) (r c : Fin g.val.1) :
    (Sum.inl r : Nodes g)≠Sum.inr c := by simp

theorem edge_bounds (g : UnitInput) (e : UnitEdges g) :
    e.val.2.1<g.val.1 ∧ e.val.2.2<g.val.1 :=
  g.property.2 e.val (List.mem_toFinset.mp e.property)

/-- Exactly one selected occurrence at EVERY row and EVERY column. This
is a condition on bits indexed by complete original edge records. -/
def Selected (g : UnitInput) (z : Selection g) : Prop :=
  (∀ r : Fin g.val.1,∃! e : UnitEdges g,e.val.2.1=r.val ∧ z e=true) ∧
  (∀ c : Fin g.val.1,∃! e : UnitEdges g,e.val.2.2=c.val ∧ z e=true)
abbrev Assignment (g : UnitInput) := {z : Selection g // Selected g z}
instance (g : UnitInput) : Fintype (Assignment g) := by
  unfold Assignment
  infer_instance

def imageBits {g : UnitInput} (m : UnitMatching g) : Selection g :=
  fun e => decide (∃ r : Fin g.val.1,m.val r=e)

theorem imageBits_self {g : UnitInput} (m : UnitMatching g) (r : Fin g.val.1) :
    imageBits m (m.val r)=true := by
  simp only [imageBits,decide_eq_true_eq]
  exact ⟨r,rfl⟩

theorem image_selected {g : UnitInput} (m : UnitMatching g) :
    Selected g (imageBits m) := by
  constructor
  · intro r
    refine ⟨m.val r,⟨m.property.1 r,imageBits_self m r⟩,?_⟩
    intro e he
    obtain ⟨r',hr'⟩ := of_decide_eq_true he.2
    have hrow : r'=r := Fin.ext (by
      calc
        r'.val = (m.val r').val.2.1 := (m.property.1 r').symm
        _ = e.val.2.1 := congrArg (fun e : UnitEdges g => e.val.2.1) hr'
        _ = r.val := he.1)
    subst r'
    exact hr'.symm
  · intro c
    obtain ⟨r,hr,hur⟩ := m.property.2 c
    refine ⟨m.val r,⟨hr,imageBits_self m r⟩,?_⟩
    intro e he
    obtain ⟨r',hr'⟩ := of_decide_eq_true he.2
    have hcol : (m.val r').val.2.2=c.val := by rw [hr']; exact he.1
    have hrow : r'=r := hur r' hcol
    subst r'
    exact hr'.symm

def chosenRow {g : UnitInput} (z : Assignment g) (r : Fin g.val.1) : UnitEdges g :=
  Classical.choose (ExistsUnique.exists (z.property.1 r))
theorem chosenRow_spec {g : UnitInput} (z : Assignment g) (r : Fin g.val.1) :
    (chosenRow z r).val.2.1=r.val ∧ z.val (chosenRow z r)=true :=
  Classical.choose_spec (ExistsUnique.exists (z.property.1 r))
theorem chosenRow_unique {g : UnitInput} (z : Assignment g) (r : Fin g.val.1)
    (e : UnitEdges g) (he : e.val.2.1=r.val ∧ z.val e=true) : e=chosenRow z r := by
  obtain ⟨e',he',hu⟩ := z.property.1 r
  exact (hu e he).trans (hu (chosenRow z r) (chosenRow_spec z r)).symm

def toMatching {g : UnitInput} (z : Assignment g) : UnitMatching g :=
  ⟨chosenRow z,by
    constructor
    · intro r
      exact (chosenRow_spec z r).1
    · intro c
      obtain ⟨e,he,hu⟩ := z.property.2 c
      let r : Fin g.val.1 := ⟨e.val.2.1,(edge_bounds g e).1⟩
      have hrow : chosenRow z r=e :=
        (chosenRow_unique z r e ⟨rfl,he.2⟩).symm
      refine ⟨r,by change (chosenRow z r).val.2.2=c.val; rw [hrow]; exact he.1,?_⟩
      intro r' hr'
      have he' : chosenRow z r'=e := hu (chosenRow z r')
        ⟨hr',(chosenRow_spec z r').2⟩
      apply Fin.ext
      calc
        r'.val = (chosenRow z r').val.2.1 := (chosenRow_spec z r').1.symm
        _ = e.val.2.1 := congrArg (fun e : UnitEdges g => e.val.2.1) he'
        _ = r.val := rfl⟩

theorem recovered_image {g : UnitInput} (z : Assignment g) :
    imageBits (toMatching z)=z.val := by
  funext e
  cases hz : z.val e with
  | false =>
      have hn : ¬∃ r : Fin g.val.1,(toMatching z).val r=e := by
        rintro ⟨r,hr⟩
        have ht := (chosenRow_spec z r).2
        change z.val ((toMatching z).val r)=true at ht
        rw [hr,hz] at ht
        cases ht
      simp [imageBits,hn,hz]
  | true =>
      let r : Fin g.val.1 := ⟨e.val.2.1,(edge_bounds g e).1⟩
      have hr : (toMatching z).val r=e :=
        (chosenRow_unique z r e ⟨rfl,hz⟩).symm
      simp only [imageBits,decide_eq_true_eq]
      exact ⟨r,hr⟩

/-- A genuine global bijection. No matching, answer, extension certificate
or expected partition identity is an input. -/
def matchingEquiv (g : UnitInput) : UnitMatching g ≃ Assignment g where
  toFun m := ⟨imageBits m,image_selected m⟩
  invFun := toMatching
  left_inv := by
    intro m
    apply Subtype.ext
    funext r
    exact (chosenRow_unique ⟨imageBits m,image_selected m⟩ r (m.val r)
      ⟨m.property.1 r,imageBits_self m r⟩).symm
  right_inv := by
    intro z
    exact Subtype.ext (recovered_image z)

def assignmentCount (g : UnitInput) : ℕ := Fintype.card (Assignment g)
theorem assignment_count (g : UnitInput) : assignmentCount g=unitCount g :=
  (Fintype.card_congr (matchingEquiv g)).symm

/-- The unweighted Boolean partition before ternary replacement. -/
def partition (g : UnitInput) : ℚ :=
  ∑ z : Selection g,if Selected g z then 1 else 0
theorem partition_count (g : UnitInput) : partition g=(unitCount g : ℚ) := by
  rw [←assignment_count g]
  unfold partition assignmentCount
  rw [Fintype.card_subtype]
  exact Finset.sum_boole _ _

/-- Missing one row is an actual zero branch, without issuing a query. -/
theorem isolated_row_zero (g : UnitInput) (r : Fin g.val.1)
    (h : ∀ e : UnitEdges g,e.val.2.1≠r.val) : unitCount g=0 := by
  letI : IsEmpty (UnitMatching g) := ⟨fun m => h (m.val r) (m.property.1 r)⟩
  exact Fintype.card_eq_zero
theorem isolated_column_zero (g : UnitInput) (c : Fin g.val.1)
    (h : ∀ e : UnitEdges g,e.val.2.2≠c.val) : unitCount g=0 := by
  letI : IsEmpty (UnitMatching g) := ⟨fun m => by
    obtain ⟨r,hr,_⟩ := m.property.2 c
    exact h (m.val r) hr⟩
  exact Fintype.card_eq_zero

end Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Incidence
