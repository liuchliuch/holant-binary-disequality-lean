import Holant.Complexity.UniversalPairReduction.ActualWitness
import Holant.Complexity.UniversalPairReduction.FieldQueries
import Holant.Complexity.UniversalPairReduction.Arithmetic
import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily

/-! Original finite algebraic families determine the answer field and the fixed
asymmetric gadget code. Neither a field presentation nor a gadget compiler is
part of the input, and no identity signature is added to the target family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.FiniteFamily
open Holant.Algebraic FixedGadgetSubstitution
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))

def family : SignatureFamily K := Set.range fun i => (⟨arity i.val,G i⟩ : AnySignature K)

private theorem signature_apply_of_sigma_eq {m n : ℕ}
    {f : Signature K m} {g : Signature K n}
    (h : (⟨m,f⟩ : AnySignature K) = ⟨n,g⟩) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast (congrArg Sigma.fst h) i)) = g x := by
  cases h
  rfl

def labelling {m : ℕ} (N : Network K m)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family G) :
    Labelling N.shape s 1 arity where
  vertex v := Classical.choose (hv v)
  vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (hv v))
  edge _ := 0

 theorem labelled_network {m : ℕ} (N : Network K m)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family G)
    (he : ∀e,N.edge e=Signature.disequality) :
    (labelling G N hv).sourceNetwork G (fun _ : Fin 1 => Signature.disequality) = N := by
  change Network.mk N.shape _ _ = Network.mk N.shape N.vertex N.edge
  congr 1
  · funext v x
    exact signature_apply_of_sigma_eq (Classical.choose_spec (hv v)) x
  · funext e
    exact (he e).symm

/-- Only original signature entries and the fixed native-X edge entries. -/
def coefficient : ExactSignatureTables.CoefficientIndex s 1 arity → K
  | .inl ⟨i,x⟩ => G i x
  | .inr (_,a,b) => Signature.disequality a b

variable (halg : ∀i x,IsAlgebraic ℚ (G i x))
include halg in
 theorem coefficient_algebraic : ∀a,IsAlgebraic ℚ (coefficient G a) := by
  intro a
  rcases a with ⟨i,x⟩ | ⟨i,a,b⟩
  · exact halg i x
  · cases a <;> cases b <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

abbrev field := familyField (coefficient G)
abbrev presentation := familyPresentation (coefficient G) (coefficient_algebraic G halg)
abbrev tables := OriginalFamily.tables (coefficient G) (coefficient_algebraic G halg)

/-- The target's decoded answer is exactly the ambient native-X Holant value. -/
theorem target_exact (r : ExactSignatureTables.Input s 1 arity) :
    (((tables G halg).evaluate (presentation G halg) r : field G) : K) =
      (r.val.realize r.property G (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 :=
  OriginalFamily.target_value_exact (coefficient G) (coefficient_algebraic G halg) r

/-- A physical fixed binary has exact coordinates in the original family field. -/
def binary {S : NetworkShape 2} (L : Labelling S s 1 arity) : BinaryTable (field G) :=
  fun a b => (L.sourceNetwork
    (fun i x => (presentation G halg).decode ((tables G halg).vertex i x))
    (fun i x y => (presentation G halg).decode ((tables G halg).edge i x y))).denote ![a,b]

 theorem binary_exact {S : NetworkShape 2} (L : Labelling S s 1 arity) (a b : Bool) :
    (binary G halg L a b : K) =
      (L.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote ![a,b] := by
  have h := OriginalFamily.macro_value_exact (coefficient G) (coefficient_algebraic G halg)
    L.template L.wellFormed ![a,b]
  rw [Labelling.denote_template] at h
  change _ = (L.template.network L.wellFormed G
    (fun _ : Fin 1 => Signature.disequality)).denote ![a,b] at h
  rw [Labelling.denote_template] at h
  exact h

/-- No extra arithmetic or compiler hypothesis: an asymmetric actual witness
has a nonzero gap in the original field and concrete ordered query reductions. -/
theorem actual_asymmetric_ingredients (f : Signature K 2)
    (hf : Gadget.Realizes (family G) .disequality f)
    (ha : f ![false,true]≠f ![true,false]) :
    ∃(S : NetworkShape 2) (L : Labelling S s 1 arity),
      (L.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote=f ∧
      binary G halg L false true ≠ binary G halg L true false ∧
      Nonempty (PolyTimeOracleReduction
        (RawClosedNetwork.validatedEncoding (s+1) 1 (extendedArity s arity))
        (presentation G halg).encoding
        (RawClosedNetwork.validatedEncoding s 1 arity) (presentation G halg).encoding
        (OrderedQueries.fieldSource (presentation G halg) (tables G halg) L (Equiv.refl _))
        ((tables G halg).evaluate (presentation G halg))) ∧
      Nonempty (PolyTimeOracleReduction
        (RawClosedNetwork.validatedEncoding (s+1) 1 (extendedArity s arity))
        (presentation G halg).encoding
        (RawClosedNetwork.validatedEncoding s 1 arity) (presentation G halg).encoding
        (OrderedQueries.fieldSource (presentation G halg) (tables G halg) L (Equiv.swap 0 1))
        ((tables G halg).evaluate (presentation G halg))) := by
  obtain ⟨N,hv,he,hN⟩ := asymmetric_ordinary_witness (family G) f hf ha
  let L := labelling G N hv
  have hL : L.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)=N := labelled_network G N hv he
  refine ⟨N.shape,L,by rw [hL,hN],?_,
    ⟨OrderedQueries.reduction (presentation G halg) (tables G halg) L (Equiv.refl _)⟩,
    ⟨OrderedQueries.reduction (presentation G halg) (tables G halg) L (Equiv.swap 0 1)⟩⟩
  intro hgap
  have heq := congrArg (fun z : field G => (z : K)) hgap
  rw [binary_exact,binary_exact,hL,hN] at heq
  exact ha heq

end Holant.Complexity.UniversalPairReduction.FiniteFamily
