import Holant.Complexity.UniversalPairReduction.BinaryInsertion
import Holant.Complexity.UniversalPairReduction.QueryFamily
import Holant.Complexity.UniversalPairReduction.Surgery.CompiledDenotation
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.SymmetricReduction

/-! Exact value equations connecting original Delta instances to the concrete
caller postprocessors. These are semantic joins for the actual compiled queries. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.ValueJoins
open Holant.Algebraic FixedGadgetSubstitution SmoothingCompiler
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s 1 arity)

abbrev signatures : (i : Fin s) → Signature K (arity i.val) := fun i x => F.decode (T.vertex i x)

variable (hnative : ∀i a b,F.decode (T.edge i a b)=Signature.disequality a b)
include hnative

 theorem target_exact (r : ExactSignatureTables.Input s 1 arity) :
    T.evaluate F r=Surgery.targetValue (signatures F T) r := by
  rw [T.evaluate_eq_decoded F]
  have he : (fun i a b => F.decode (T.edge i a b))=(fun _ : Fin 1 => (Signature.disequality : BinaryTable K)) :=
    funext fun i => funext fun a => funext (hnative i a)
  rw [he]
  rfl

 theorem corrected_native (r : Input s arity) :
    corrected (T.evaluate F (Surgery.query r),flags r)=BinaryFamily.value (signatures F T) Signature.disequality r := by
  rw [target_exact F T hnative,Surgery.compiled_native_value]
  unfold corrected flags
  cases hc : (Smoothing.compile s r.val).circle <;> simp

 theorem symmetric_exact
    (hs : ∀f : Signature K 2,Gadget.Realizes (BinaryFamily.family (signatures F T)) .disequality f →
      f ![false,true]=f ![true,false]) (r : Input s arity) :
    BinaryFamily.value (signatures F T) BinaryTable.delta r=symmetricReducedValue F T r := by
  rcases Surgery.selected r with ⟨hz,hcompile,hlabels⟩|⟨v,p,q,hv,hrow,hcount,hcompile⟩
  · rw [Surgery.zero_value (signatures F T) r BinaryTable.delta hz]
    unfold symmetricReducedValue symmetricPost flags
    simp only [hz,zero_ne_one,decide_false,Bool.false_eq_true,ite_false]
    exact (target_exact F T hnative _).symm
  · unfold symmetricReducedValue symmetricPost
    have hf : (flags r).2=true := by simp [flags,hcount]
    rw [hf,if_pos rfl,corrected_native F T hnative,
      BinaryFamily.delta_value (signatures F T) r v hv,
      BinaryFamily.native_value (signatures F T) r v hv]
    exact BinaryTable.reconstruct_symmetric _ (BinaryFamily.symmetric_hole (signatures F T) r v hv hs)

 theorem asymmetric_exact {S : NetworkShape 2} (L : Labelling S s 1 arity)
    (ha : QueryFamily.binary (signatures F T) L (Equiv.refl _) false true ≠
      QueryFamily.binary (signatures F T) L (Equiv.refl _) true false)
    (r : Input s arity) :
    BinaryFamily.value (signatures F T) BinaryTable.delta r =
      asymmetricPost (QueryFamily.binary (signatures F T) L (Equiv.refl _) false true)
        (QueryFamily.binary (signatures F T) L (Equiv.refl _) true false)
        (T.evaluate F (Surgery.query r),
          (T.evaluate F (OrderedQueries.plus L (forget s arity r)),
            (T.evaluate F (OrderedQueries.minus L (forget s arity r)),flags r))) := by
  rcases Surgery.selected r with ⟨hz,hcompile,hlabels⟩|⟨v,p,q,hv,hrow,hcount,hcompile⟩
  · rw [Surgery.zero_value (signatures F T) r BinaryTable.delta hz]
    unfold asymmetricPost flags
    simp only [hz,zero_ne_one,decide_false,Bool.false_eq_true,ite_false]
    exact (target_exact F T hnative _).symm
  · unfold asymmetricPost
    have hf : (flags r).2=true := by simp [flags,hcount]
    rw [hf,if_pos rfl]
    rw [corrected_native F T hnative,
      target_exact F T hnative (OrderedQueries.plus L (forget s arity r)),
      target_exact F T hnative (OrderedQueries.minus L (forget s arity r))]
    rw [QueryFamily.query_value,QueryFamily.query_value,QueryFamily.binary_minus]
    rw [BinaryFamily.delta_value (signatures F T) r v hv,
      BinaryFamily.native_value (signatures F T) r v hv,
      BinaryFamily.insert_value (signatures F T) r v hv,
      BinaryFamily.insert_value (signatures F T) r v hv]
    exact BinaryTable.reconstruct_asymmetric _ _ ha

end Holant.Complexity.UniversalPairReduction.ValueJoins
