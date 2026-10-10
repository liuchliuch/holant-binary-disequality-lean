import Holant.Proofs.Closure.ClosureWeightedPencilRoots

/-! Analytic enlargement of the proved pencil to twice the phase order.
Extra phases are mathematical consequences, not asserted current resources.
All zero samples and both orientations of a proportional pencil are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain ClosureRootPencil
open scoped BigOperators

theorem product_double {m : ℕ} {q : Signature ℂ 4} (actual : RootProduct m q) :
    RootProduct (2*m) q := by
  obtain ⟨P⟩ := actual
  exact ⟨{ P with rooted := fun e => root_double (P.rooted e) }⟩

theorem product_scale {k : ℕ} {q : Signature ℂ 4} (actual : RootProduct k q)
    (c : ℂ) (nonzero : c≠0) : RootProduct k (c • q) := by
  obtain ⟨P⟩ := actual
  refine ⟨{ P with scalar := c*P.scalar
                   nonzero := mul_ne_zero nonzero P.nonzero
                   equation := ?_ }⟩
  funext x
  rw [Pi.smul_apply,smul_eq_mul,congrFun P.equation x]
  ring

theorem product_gauge {k : ℕ} {q : Signature ℂ 4} (actual : RootProduct k q)
    (r : Fin 4 → ℂ) (nonzero : ∀ i,r i≠0) (roots : ∀ i,r i^k=1) :
    RootProduct k (WeightedGauge.gauge r q) := by
  obtain ⟨P⟩ := actual
  have equation : q=P.scalar • pairTensor P.ports (P.matrix 0) (P.matrix 1) := by
    funext x
    rw [congrFun P.equation x]
    simp [pairTensor,Fin.prod_univ_two]
  have linear : WeightedGauge.gauge r (P.scalar • pairTensor P.ports (P.matrix 0) (P.matrix 1))=
      P.scalar • WeightedGauge.gauge r (pairTensor P.ports (P.matrix 0) (P.matrix 1)) := by
    funext x
    change _*(P.scalar*_)=P.scalar*(_*_)
    ring
  refine ⟨{
    ports := P.ports
    matrix := fun e => portBinary r P.ports e (P.matrix e)
    scalar := P.scalar
    nonzero := P.nonzero
    rooted := fun e => portBinary_root r nonzero roots _ e _ (P.rooted e)
    equation := ?_ }⟩
  calc
    _=WeightedGauge.gauge r (P.scalar • pairTensor P.ports (P.matrix 0) (P.matrix 1)) :=
      congrArg (WeightedGauge.gauge r) equation
    _=P.scalar • WeightedGauge.gauge r (pairTensor P.ports (P.matrix 0) (P.matrix 1)) := linear
    _=_ := by
      rw [gauge_pairTensor]
      funext x
      simp [pairTensor,Fin.prod_univ_two]

theorem proportional_all_samples {k : ℕ} (U V : Signature ℂ 4)
    (dependent : ClosureSixPort.DependentEndpoints U V) (t0 : ℂ)
    (anchor : RootProduct k (pencil U V t0)) :
    ∀ t : ℂ,pencil U V t=0 ∨ RootProduct k (pencil U V t) := by
  obtain ⟨P⟩ := anchor
  rcases dependent with ⟨c,relation⟩ | ⟨c,relation⟩
  · have live : 1+t0*c≠0 := by
      intro zero
      apply P.nonzero_tensor
      funext x
      rw [relation]
      change U x+t0*(c*U x)=0
      calc
        _=(1+t0*c)*U x := by ring
        _=0 := by rw [zero,zero_mul]
    intro t
    by_cases zero : 1+t*c=0
    · left
      funext x
      rw [relation]
      change U x+t*(c*U x)=0
      calc
        _=(1+t*c)*U x := by ring
        _=0 := by rw [zero,zero_mul]
    · right
      have equation : pencil U V t=((1+t*c)/(1+t0*c)) • pencil U V t0 := by
        funext x
        rw [relation]
        change U x+t*(c*U x)=((1+t*c)/(1+t0*c))*(U x+t0*(c*U x))
        calc
          _=(1+t*c)*U x := by ring
          _=(((1+t*c)/(1+t0*c))*(1+t0*c))*U x := by rw [div_mul_cancel₀ _ live]
          _=_ := by ring
      rw [equation]
      exact product_scale ⟨P⟩ _ (div_ne_zero zero live)
  · have live : c+t0≠0 := by
      intro zero
      apply P.nonzero_tensor
      funext x
      rw [relation]
      change c*V x+t0*V x=0
      calc
        _=(c+t0)*V x := by ring
        _=0 := by rw [zero,zero_mul]
    intro t
    by_cases zero : c+t=0
    · left
      funext x
      rw [relation]
      change c*V x+t*V x=0
      calc
        _=(c+t)*V x := by ring
        _=0 := by rw [zero,zero_mul]
    · right
      have equation : pencil U V t=((c+t)/(c+t0)) • pencil U V t0 := by
        funext x
        rw [relation]
        change c*V x+t*V x=((c+t)/(c+t0))*(c*V x+t0*V x)
        calc
          _=(c+t)*V x := by ring
          _=(((c+t)/(c+t0))*(c+t0))*V x := by rw [div_mul_cancel₀ _ live]
          _=_ := by ring
      rw [equation]
      exact product_scale ⟨P⟩ _ (div_ne_zero zero live)

theorem complementary_one_entry {m : ℕ} {U V : Signature ℂ 4}
    (C : ClosureRootPencil.Complementary m U V) (a : Bool) :
    binaryPencil C.ruling.variable0 C.ruling.variable1 1
      (C.orientation^^a) ((C.orientation^^a)^^C.parity)=C.coefficient a := by
  rw [C.variable0,C.variable1]
  cases C.parity <;> cases C.orientation <;> cases a <;>
    simp [binaryPencil,parityAxis,ClosureRootPencil.Complementary.coefficient]

theorem complementary_coefficient_ratio {m : ℕ} {U V : Signature ℂ 4}
    (C : ClosureRootPencil.Complementary m U V) :
    (C.coefficient1/C.coefficient0)^m=1 := by
  have live : binaryPencil C.ruling.variable0 C.ruling.variable1 1≠0 := by
    intro zero
    have entry := complementary_one_entry C false
    rw [zero] at entry
    exact C.coefficient0_nonzero entry.symm
  have rooted := (C.ruling.samples 1 (by simp)).resolve_left live
  have first : binaryPencil C.ruling.variable0 C.ruling.variable1 1
      (C.orientation^^false) ((C.orientation^^false)^^C.parity)≠0 := by
    rw [complementary_one_entry]
    exact C.coefficient0_nonzero
  have second : binaryPencil C.ruling.variable0 C.ruling.variable1 1
      (C.orientation^^true) ((C.orientation^^true)^^C.parity)≠0 := by
    rw [complementary_one_entry]
    exact C.coefficient1_nonzero
  have ratio := root_ratio rooted (C.orientation^^true) ((C.orientation^^true)^^C.parity)
    (C.orientation^^false) ((C.orientation^^false)^^C.parity) second first
  simpa only [complementary_one_entry,ClosureRootPencil.Complementary.coefficient,
    Bool.false_eq_true,ite_false,ite_true] using ratio

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
