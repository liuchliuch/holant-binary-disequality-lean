import Holant.Proofs.Reductions.GeneralExtraction.RecursiveMachine


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation.PrefixMachine
open Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.GeneralExtraction
open GeneralPowerExposure
variable {K : Type} [Field K] [Algebra ℚ K] {d s N : ℕ} {A : ℕ → ℕ}
variable (T : (i : ℕ) → Signature K (A i))

def family (n : ℕ) (i : Fin (s+n)) : Signature K (A i.val) := T i.val

theorem extension (n : ℕ) :
    RetainedPairReduction.extended (family (s:=s) T n) (T (s+n)) = family (s:=s) T (n+1) := by
  funext i x
  by_cases hi : i.val < s+n
  · exact congrFun (GeneralOriginalQuery.source_old (family (s:=s) T n) (T (s+n)) ⟨i.val,hi⟩) x
  · have he : i = ⟨s+n,by omega⟩ := Fin.ext (by change i.val = s+n; omega)
    revert x
    rw [he]
    intro x
    exact congrFun (GeneralOriginalQuery.source_new (family (s:=s) T n) (T (s+n))) x

def labels {m : ℕ} {S : NetworkShape m} (L : Labelling S s 1 A) (n : ℕ) :
    Labelling S (s+n) 1 A where
  vertex v := ⟨(L.vertex v).val, by have := (L.vertex v).isLt; omega⟩
  vertex_arity := L.vertex_arity
  edge := L.edge

def weaken {m : ℕ} {f : Signature K m} (P : PowerMacro (family (s:=s) T 0) f) (n : ℕ) :
    PowerMacro (family (s:=s) T n) f where
  exponent := P.exponent
  positive := P.positive
  scale := P.scale
  scale_ne_zero := P.scale_ne_zero
  network := P.network
  labels := labels P.labels n
  value := by
    rw [Labelling.denote_template]
    have he : ((labels P.labels n).sourceNetwork (family (s:=s) T n) (fun _ => Signature.disequality)).denote =
        (P.labels.sourceNetwork (family (s:=s) T 0) (fun _ => Signature.disequality)).denote := by
      apply Network.denote_congr
      · intro v x; rfl
      · intro e a b; rfl
    rw [he, ← Labelling.denote_template]
    exact P.value

variable (M : (j : Fin N) → PowerMacro (family (s:=s) T 0) (T (s+j.val)))

def chain : (n : ℕ) → n ≤ N → RecursiveMachine.Chain (family (s:=s) T 0) (family (s:=s) T n)
  | 0, _ => .nil
  | n+1, hn => by
      have C := RecursiveMachine.Chain.snoc (chain n (by omega)) (T (s+n))
        (weaken T (M ⟨n,by omega⟩) n)
      rw [extension T n] at C
      exact C

variable (F : FixedField K d)
def reduction := RecursiveMachine.reduction F (chain T M N le_rfl)

/-- Interpret the already stored chain with a REAL terminal machine. In the
forest endpoint the terminal is the original-field transport, constructed
from an inclusion of coefficient fields; it is not an extraction assumption. -/
def withTerminal {Q B : Type} {eq : Computability.Encoding Q Bool} {eb : Computability.Encoding B Bool}
    {g : Q → B}
    (base : PolyTimeOracleReduction (RawClosedNetwork.validatedEncoding s 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F (family (s:=s) T 0)).evaluate F) g)
    {n : ℕ} {H : (i : Fin n) → Signature K (A i.val)}
    (C : RecursiveMachine.Chain (family (s:=s) T 0) H) :
    PolyTimeOracleReduction (RawClosedNetwork.validatedEncoding n 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F H).evaluate F) g :=
  match C with
  | .nil => base
  | .snoc previous f P => (RecursiveMachine.step F f P).compose (withTerminal base previous)

end Holant.LocalDrafts.Hardness.FactorSaturation.PrefixMachine
