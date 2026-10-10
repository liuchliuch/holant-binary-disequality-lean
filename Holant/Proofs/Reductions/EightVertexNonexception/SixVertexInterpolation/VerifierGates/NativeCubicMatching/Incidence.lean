import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Extensions
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Incidence
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Compiler


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Holant
open scoped BigOperators
open WeightedMatchingInterpolation
namespace OldIncidence
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Incidence
  (Selection Selected Assignment matchingEquiv assignment_count partition_count)
end OldIncidence
namespace OldCompiler
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Compiler
  (nodes ports ports_bound virtual virtual_endpoints occurrence occurrenceEquiv zeroTest zeroTest_count)
end OldCompiler
namespace Incidence

abbrev Ends (g : UnitInput) := UnitEdges g → Bool × Bool
instance (g : UnitInput) : Fintype (Ends g) := by
  letI : Fintype (Bool × Bool) := @instFintypeProd Bool Bool Bool.fintype Bool.fintype
  unfold Ends
  infer_instance
def Supported (g : UnitInput) (z : Ends g) : Prop :=
  (∀ e,(z e).2=!(z e).1) ∧
  (∀ r : Fin g.val.1,∃! e : UnitEdges g,e.val.2.1=r.val ∧ (z e).1=true) ∧
  (∀ c : Fin g.val.1,∃! e : UnitEdges g,e.val.2.2=c.val ∧ (z e).2=false)
def lift {g : UnitInput} (z : OldIncidence.Selection g) : Ends g := fun e => (z e,!z e)

theorem lift_supported {g : UnitInput} (z : OldIncidence.Selection g) :
    Supported g (lift z) ↔ OldIncidence.Selected g z := by
  simp [Supported,lift,OldIncidence.Selected]

theorem supported_left {g : UnitInput} (z : Ends g) (hz : Supported g z) :
    OldIncidence.Selected g (fun e => (z e).1) := by
  refine ⟨hz.2.1,?_⟩
  intro c
  have hbit (e : UnitEdges g) : (z e).2=false ↔ (z e).1=true := by
    rw [hz.1 e]
    simp
  simpa only [hbit] using hz.2.2 c

def assignments (g : UnitInput) : {z : Ends g // Supported g z} ≃ OldIncidence.Assignment g where
  toFun z := ⟨fun e => (z.val e).1,supported_left z.val z.property⟩
  invFun z := ⟨lift z.val,(lift_supported z.val).mpr z.property⟩
  left_inv z := by
    apply Subtype.ext
    funext e
    exact Prod.ext rfl (z.property.1 e).symm
  right_inv z := Subtype.ext rfl

def partition (g : UnitInput) : ℚ := ∑ z : Ends g,if Supported g z then 1 else 0
theorem partition_count (g : UnitInput) : partition g=unitValue g := by
  classical
  have hc : Fintype.card {z : Ends g // Supported g z}=unitCount g :=
    (Fintype.card_congr (assignments g)).trans (OldIncidence.assignment_count g)
  unfold partition unitValue
  rw [←hc,Fintype.card_subtype]
  exact Finset.sum_boole _ _

/-- List POSITION, not the record's ID pair, is the emitted edge number. -/
def occurrenceBits (g : UnitInput) (z : Ends g) (p : Fin g.val.2.length × Bool) : Bool :=
  if p.2 then (z (OldCompiler.occurrence g p.1)).2
  else (z (OldCompiler.occurrence g p.1)).1
theorem physical_cross_edge (g : UnitInput) (z : Ends g) (hz : Supported g z)
    (i : Fin g.val.2.length) :
    (Signature.disequality (occurrenceBits g z (i,false))
      (occurrenceBits g z (i,true)) : ℚ)=1 := by
  simp only [occurrenceBits,Bool.false_eq_true,if_false,if_true,hz.1]
  cases h : (z (OldCompiler.occurrence g i)).1 <;> simp [Signature.disequality,h]

def paddingCount (g : UnitInput) : ℕ :=
  ((OldCompiler.nodes g).map (fun p => Extensions.padding (OldCompiler.ports g p.1 p.2).length)).sum
theorem padding_bound (g : UnitInput) : paddingCount g≤6*g.val.1 := by
  have h : ∀ xs : List (Bool × ℕ),
      (xs.map (fun p => Extensions.padding (OldCompiler.ports g p.1 p.2).length)).sum≤3*xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons p xs ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        have := Extensions.padding_le (OldCompiler.ports g p.1 p.2).length
        omega
  have hn : (OldCompiler.nodes g).length=2*g.val.1 := by
    simp [OldCompiler.nodes]
    omega
  exact (h _).trans_eq (by rw [hn]; omega)
theorem padding_input_bound (g : UnitInput) : paddingCount g≤6*(unitEncoding.encode g).length :=
  (padding_bound g).trans (Nat.mul_le_mul_left 6 (unit_input_counts g).1)

theorem isolated_guard (g : UnitInput) (h : OldCompiler.zeroTest g=true) : unitValue g=0 := by
  change (unitCount g : ℚ)=0
  rw [OldCompiler.zeroTest_count g h,Nat.cast_zero]

end Incidence
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
