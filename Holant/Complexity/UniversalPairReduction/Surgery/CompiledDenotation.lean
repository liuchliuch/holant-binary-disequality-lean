import Holant.Complexity.UniversalPairReduction.Surgery.Denotation
import Holant.Complexity.UniversalPairReduction.Surgery.Selection

/-! Exact original-input semantics for the concrete smoothing compiler, including
its internally discovered zero-occurrence and circle cases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.Surgery
open Smoothing Choice FixedGadgetSubstitution
variable {K : Type*} [CommSemiring K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val)) (r : Input s arity)

 theorem target_evaluate (a : {r : RawClosedNetwork // r.WellFormed s 1 arity}) :
    targetValue G a=Choice.evaluate (Choice.table G) a.val.edges.length a.val.vertices :=
  Choice.denote_eq_evaluate a.val a.property G

 theorem zero_value (B : BinaryTable K) (hz : occurrences s r.val=0) :
    BinaryFamily.value G B r=targetValue G (query r) := by
  rcases selected r with ⟨hzero,hcompile,hlabels⟩|⟨v,p,q,hv,hrow,hcount,hcompile⟩
  · rw [BinaryFamily.value_evaluate,BinaryFamily.evaluate_old G B _ _ hlabels,target_evaluate]
    simp only [query,hcompile]
  · omega

 theorem compiled_native_value :
    BinaryFamily.value G Signature.disequality r =
      (if (Smoothing.compile s r.val).circle then 2 else 1)*targetValue G (query r) := by
  rcases selected r with ⟨hz,hcompile,hlabels⟩|⟨v,p,q,hv,hrow,hcount,hcompile⟩
  · rw [zero_value G r Signature.disequality hz,hcompile]
    simp
  · have hq : query r=queryAt r v hv p q hrow := Subtype.ext (congrArg Result.query hcompile)
    rw [hcompile,hq]
    exact native_value G r v hv p q hrow

 theorem compiled_loop_value (B : BinaryTable K) (hc : (Smoothing.compile s r.val).circle=true) :
    BinaryFamily.value G B r=(B false true+B true false)*targetValue G (query r) := by
  rcases selected r with ⟨hz,hcompile,hlabels⟩|⟨v,p,q,hv,hrow,hcount,hcompile⟩
  · simp [hcompile] at hc
  · have he : p.1=q.1 := by
      rw [hcompile] at hc
      unfold smoothAt at hc
      split_ifs at hc with he
      exact he
    have hq : query r=queryAt r v hv p q hrow := Subtype.ext (congrArg Result.query hcompile)
    rw [hq]
    exact loop_value G r v hv p q hrow B he

 theorem compiled_delta_loop (hc : (Smoothing.compile s r.val).circle=true) :
    BinaryFamily.value G BinaryTable.delta r=targetValue G (query r) := by
  rw [compiled_loop_value G r BinaryTable.delta hc]
  simp [BinaryTable.delta]

end Holant.Complexity.UniversalPairReduction.Surgery
