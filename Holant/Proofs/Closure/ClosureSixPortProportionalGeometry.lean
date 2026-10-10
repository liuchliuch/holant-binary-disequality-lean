import Holant.Proofs.Closure.ClosureSixPortProportional
import Holant.Proofs.Closure.ClosureSixPortComplementary
import Holant.Proofs.Closure.ClosureSixPortBooleanGauge

/-! Ordered-port support normalization for a literal complementary-axis
ruling. Only the given endpoints' entry equations and actual nonsingular
fixed root factor are used. No transformed tensor is asserted retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective
namespace Proportional

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cSupport_coordinates (edge : Fin 6) (a b o z : Bool) (x : Word 4) :
    x ∈ CSupport edge a b o z ↔
      x (fixedPositions edge 1)=(x (fixedPositions edge 0) ^^ a) ∧
      x (varyingPositions edge 0)=(o ^^ z) ∧
      x (varyingPositions edge 1)=((o ^^ z) ^^ b) := by
  revert x
  fin_cases edge <;> cases a <;> cases b <;> cases o <;> cases z <;> decide

theorem pairing_complementary_flat : ∀ i j k l : Fin 4,
    (i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l) → ∀ a b o : Bool,
    ∃ edge : Fin 6, ∃ r s v : Bool, ∀ z : Bool, ∀ x : Word 4,
      ((x i ^^ x j)=a ∧ x k=(o ^^ z) ∧ x l=((o ^^ z) ^^ b)) ↔
        x ∈ CSupport edge r s v z := by
  intro i j k l distinct a b o
  obtain ⟨edge,reverseFixed,reverseVarying,hi,hj,hk,hl⟩ :=
    four_positions_exhaustive i j k l distinct.1 distinct.2.1 distinct.2.2.1
      distinct.2.2.2.1 distinct.2.2.2.2.1 distinct.2.2.2.2.2
  refine ⟨edge,a,b,o ^^ (if reverseVarying then b else false),?_⟩
  intro z x
  rw [cSupport_coordinates,hi,hj,hk,hl]
  have xor_form (u v p : Bool) : (u ^^ v)=p ↔ v=(u ^^ p) := by
    cases u <;> cases v <;> cases p <;> decide
  rw [xor_form]
  have fixed := fixed_coordinate_gauge reverseFixed (x (fixedPositions edge 0))
    (x (fixedPositions edge 1)) false false a
  have varying := varying_coordinate_gauge reverseVarying (x (varyingPositions edge 0))
    (x (varyingPositions edge 1)) false false o z b
  cases reverseFixed <;> cases reverseVarying <;>
    simpa only [Bool.xor_false,Bool.false_xor,Bool.false_eq_true,reduceCtorEq,ite_false,ite_true] using
      (and_congr fixed varying)

/-- Literal complementary-axis matrices have one nonzero entry at each
endpoint, on bitwise complementary positions. The coefficients themselves
are preserved by the ruling's equations and are never assumed equal. -/
def ComplementaryBinarySupport (V : Bool → Kernel ℂ) (b o : Bool) : Prop :=
  ∀ z r s, V z r s ≠ 0 ↔ r=(o ^^ z) ∧ s=((o ^^ z) ^^ b)

theorem complementary_ports_support {m : ℕ} (h : Signature ℂ 6)
    (e : Equiv.Perm (Fin 6)) (p : Bool) (ports : (Fin 2 × Bool) ≃ Fin 4)
    (fixed : Kernel ℂ) (rooted : IsRootMonomial m fixed) (V : Bool → Kernel ℂ)
    (b o : Bool) (axis : ComplementaryBinarySupport V b o)
    (equations : ∀ z x, sliceSix h e p z x =
      fixed (x (ports (0,false))) (x (ports (0,true))) *
        V z (x (ports (1,false))) (x (ports (1,true)))) :
    ∃ edge : Fin 6, ∃ a b o : Bool, ComplementarySector h e p edge a b o := by
  obtain ⟨a,fixedSupport⟩ := ClosureRootPencil.root_support rooted
  let i := ports (0,false)
  let j := ports (0,true)
  let k := ports (1,false)
  let l := ports (1,true)
  have distinct : i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    all_goals intro he; have := ports.injective he; contradiction
  obtain ⟨edge,r,s,v,shape⟩ := pairing_complementary_flat i j k l distinct a b o
  refine ⟨edge,r,s,v,?_⟩
  intro z x
  rw [equations,mul_ne_zero_iff,fixedSupport,axis]
  have xor_form (a b p : Bool) : b=(a ^^ p) ↔ (a ^^ b)=p := by
    cases a <;> cases b <;> cases p <;> decide
  simpa only [xor_form,i,j,k,l,and_assoc] using shape z x

/-- A genuine literal P/C or C/P ruling has an actual forbidden ordered
card. The geometric support normalization is constructed internally. -/
theorem proportional_complementary_ports_impossible {m : ℕ} (hm : 3 ≤ m)
    (h : Signature ℂ 6) (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (dependent : DependentEndpoints (sliceSix h e p false) (sliceSix h e p true))
    (nonzero : ¬ZeroSector h e p) (ports : (Fin 2 × Bool) ≃ Fin 4)
    (fixed : Kernel ℂ) (rooted : IsRootMonomial m fixed) (V : Bool → Kernel ℂ)
    (b o : Bool) (axis : ComplementaryBinarySupport V b o)
    (equations : ∀ z x, sliceSix h e (!p) z x =
      fixed (x (ports (0,false))) (x (ports (0,true))) *
        V z (x (ports (1,false))) (x (ports (1,true)))) : False := by
  obtain ⟨edge,a,b,o,complementary⟩ :=
    complementary_ports_support h e (!p) ports fixed rooted V b o axis equations
  exact proportional_complementary_impossible hm h deck e p dependent nonzero
    edge a b o complementary

/-- Exact consumer of the SAME internally generated complementary-sector
payload used by the Z/C and C/C routes. No separate support classifier is
accepted or selected. Both transposed P/C orientations use the Boolean tag. -/
theorem actual_proportional_complementary_impossible {m : ℕ} (hm : 3 ≤ m)
    (h : Signature ℂ 6) (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (dependent : DependentEndpoints (sliceSix h e p false) (sliceSix h e p true))
    (nonzero : ¬ZeroSector h e p)
    (D : Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort.ComplementarySector m h e (!p)) :
    False := by
  apply proportional_complementary_ports_impossible hm h deck e p dependent nonzero
    D.ports D.fixed D.rooted (fun z => D.coefficient z • parityAxis D.parity (D.orientation^^z))
    D.parity D.orientation
  · intro z r s
    exact scaled_axis_support D.parity (D.orientation^^z) r s _ (D.nonzero z)
  · exact D.endpoints

end Proportional
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
