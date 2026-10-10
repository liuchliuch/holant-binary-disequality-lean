import Holant.Proofs.Algorithms.TransformRecognition.PositiveWitnessSearch
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Resources
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.RootSearchDriver.Height


namespace Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open ComplexIsolation
open Holant.LocalDrafts.MainChain.TransformRecognition

abbrev Term := ℕ × List ℕ
abbrev Equation := List Term
abbrev System := List Equation
abbrev naturalsEncoding := framedListEncoding encodingNatBool
abbrev termEncoding := pairEncoding encodingNatBool naturalsEncoding
abbrev equationEncoding := framedListEncoding termEncoding
abbrev systemEncoding := framedListEncoding equationEncoding
abbrev vectorsEncoding := framedListEncoding CommonFieldMachine.coordinatesEncoding

structure Request where
  family : CommonFieldMachine.Request
  equations : System
  values : List (List ℚ)
  certificate : Certificate

abbrev Wire := CommonFieldMachine.Request × (System × (List (List ℚ) × Certificate))
abbrev wireEncoding := pairEncoding CommonFieldMachine.requestEncoding
  (pairEncoding systemEncoding (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding))
def Request.wire (r : Request) : Wire := (r.family,r.equations,r.values,r.certificate)
def Request.unwire (w : Wire) : Request := ⟨w.1,w.2.1,w.2.2.1,w.2.2.2⟩
def requestEncoding : Encoding Request Bool where
  encode r := wireEncoding.encode r.wire
  decode w := (wireEncoding.decode w).map Request.unwire
  decode_encode r := by
    change (wireEncoding.decode (wireEncoding.encode r.wire)).map Request.unwire = some r
    rw [wireEncoding.decode_encode]
    cases r
    rfl

def encodeTerm {m n : ℕ} (t : EncodedSystem.Term m n) : Term := (t.1.val,List.ofFn t.2)
def encodeSystem {m n : ℕ} (s : EncodedSystem.System m n) : System := s.map (List.map encodeTerm)

theorem encodeTerm_injective {m n : ℕ} : Function.Injective (@encodeTerm m n) := by
  intro a b h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact List.ofFn_injective (congrArg Prod.snd h)

theorem encodeSystem_injective {m n : ℕ} : Function.Injective (@encodeSystem m n) :=
  List.map_injective_iff.mpr (List.map_injective_iff.mpr encodeTerm_injective)

theorem term_bytes {m n : ℕ} (t : EncodedSystem.Term m n) :
    termEncoding.encode (encodeTerm t) = frame (encodingNatBool.encode t.1.val) ++
      naturalsEncoding.encode (List.ofFn t.2) := rfl

def fromSource {m k : ℕ} (target : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) : Request :=
  ⟨CommonFieldMachine.fromFamily a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 target,
    encodeSystem s,List.ofFn (fun i => List.ofFn (a.1.2.2.2.2 i)),a.2⟩

def Request.shape (r : Request) : Bool :=
  r.family.shape && decide (5 ≤ r.values.length) &&
    r.values.all (fun v => decide (v.length = r.family.dimension)) &&
    r.equations.all (fun e => e.all (fun t =>
      decide (t.1 < r.family.targets.length ∧ t.2.length = r.values.length)))

theorem fromSource_shape {m k : ℕ} (t : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    (fromSource t s a).shape = true := by
  simp only [Request.shape,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨⟨⟨CommonFieldMachine.fromFamily_shape _ _ _ _,?_⟩,?_⟩,?_⟩
  · simp [fromSource]
  · intro v hv
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hv
    subst v
    simp [fromSource,CommonFieldMachine.fromFamily]
  · intro e he
    obtain ⟨e',he',heq⟩ := List.mem_map.mp he
    subst e
    intro u hu
    obtain ⟨u',hu',huq⟩ := List.mem_map.mp hu
    subst u
    change u'.1.val < (List.ofFn t).length ∧ (List.ofFn u'.2).length =
      (List.ofFn (fun i => List.ofFn (a.1.2.2.2.2 i))).length
    simp only [List.length_ofFn]
    exact ⟨u'.1.isLt,True.intro⟩

theorem shape_iff (r : Request) : r.shape = true ↔
    r.family.shape = true ∧ 5 ≤ r.values.length ∧
      (∀ v ∈ r.values, v.length = r.family.dimension) ∧
      ∀ e ∈ r.equations, ∀ t ∈ e, t.1 < r.family.targets.length ∧ t.2.length = r.values.length := by
  simp [Request.shape,Bool.and_eq_true,List.all_eq_true,and_assoc]

theorem request_faithful : Function.Injective requestEncoding.encode := requestEncoding.encode_injective
theorem source_decode_encode {m k : ℕ} (t : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    requestEncoding.decode (requestEncoding.encode (fromSource t s a)) = some (fromSource t s a) :=
  requestEncoding.decode_encode _
theorem original_equations {m k : ℕ} (t : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    (fromSource t s a).equations = s.map (fun e => e.map (fun u => (u.1.val,List.ofFn u.2))) := rfl
theorem original_targets {m k : ℕ} (t : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    (fromSource t s a).family.targets = List.ofFn t := rfl
theorem original_exponents {m n : ℕ} (t : EncodedSystem.Term m n) (i : Fin n) :
    (encodeTerm t).2.getD i.val 0 = t.2 i := by
  rw [encodeTerm,List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

theorem getD_ofFn {A : Type} {n : ℕ} (v : Fin n → A) (i : Fin n) (default : A) :
    (List.ofFn v).getD i.val default = v i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

end Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine
