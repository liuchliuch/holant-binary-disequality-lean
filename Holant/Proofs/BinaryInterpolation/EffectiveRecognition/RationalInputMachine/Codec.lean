import Holant.Proofs.Algorithms.TransformRecognition.RationalInputSystem
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Resources
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrue


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition

abbrev Term := List ℕ × ℚ
abbrev Row := List Term
abbrev Body := List Row
abbrev termEncoding := pairEncoding NegativeCertificateMachine.exponentEncoding rationalEncoding
abbrev rowEncoding := framedListEncoding termEncoding
abbrev bodyEncoding := framedListEncoding rowEncoding
abbrev addressesEncoding := framedListEncoding encodingNatBool

structure Input where
  «variables» : ℕ
  original : List RootCode
  body : Body
  addresses : List ℕ

abbrev Wire := ℕ × (List RootCode × (Body × List ℕ))
abbrev lastEncoding := pairEncoding bodyEncoding addressesEncoding
abbrev tailEncoding := pairEncoding CommonFieldMachine.rootsEncoding lastEncoding
abbrev wireEncoding := pairEncoding encodingNatBool tailEncoding
def Input.wire (r : Input) : Wire := (r.variables,r.original,r.body,r.addresses)
def Input.unwire (w : Wire) : Input := ⟨w.1,w.2.1,w.2.2.1,w.2.2.2⟩
def encoding : Encoding Input Bool where
  encode r := wireEncoding.encode r.wire
  decode w := (wireEncoding.decode w).map Input.unwire
  decode_encode r := by
    change (wireEncoding.decode (wireEncoding.encode r.wire)).map Input.unwire = some r
    rw [wireEncoding.decode_encode]
    cases r
    rfl

theorem faithful : Function.Injective encoding.encode := encoding.encode_injective

def termWire {n : ℕ} (t : Sparse.Term n 1) : Term := (List.ofFn t.1,t.2 0)
def rowWire {n : ℕ} (p : Sparse.Poly n 1) : Row := p.map termWire
def bodyWire {n : ℕ} (S : List (Sparse.Poly n 1)) : Body := S.map rowWire
def fromSource {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) : Input :=
  ⟨5+k,List.ofFn original,bodyWire S,List.ofFn (fun i => (address i).val)⟩

def coefficients (S : Body) : List ℚ := 1 :: -1 :: S.flatMap (fun p => p.map Prod.snd)
def bodyTerm (m : ℕ) (cs : List ℚ) (t : Term) : NegativeCertificateMachine.SourceTerm :=
  (m+cs.idxOf t.2,t.1)
def bodyRows (r : Input) : NegativeCertificateMachine.System :=
  r.body.map (fun p => p.map (bodyTerm r.original.length (coefficients r.body)))
def zero (n : ℕ) : List ℕ := List.replicate n 0
def hit (n j : ℕ) : List ℕ := (List.range n).map (fun i => if i=j then 1 else 0)
def triple (n a b c : ℕ) : List ℕ :=
  (List.range n).map (fun i => (if i=a then 1 else 0)+(if i=b then 1 else 0)+(if i=c then 1 else 0))
def binding (r : Input) (i : ℕ) : NegativeCertificateMachine.Equation :=
  [(i,zero r.variables),(r.original.length+1,hit r.variables (r.addresses.getD i 0))]
def bindings (r : Input) : NegativeCertificateMachine.System :=
  (List.range r.original.length).map (binding r)
def guard (r : Input) : NegativeCertificateMachine.Equation :=
  [(r.original.length,triple r.variables 4 0 3),
   (r.original.length+1,triple r.variables 4 1 2),
   (r.original.length+1,zero r.variables)]
def targets (r : Input) : List RootCode := r.original ++ (coefficients r.body).map RationalRootCode.code
def request (r : Input) : NegativeCatalogueMachine.Request :=
  ⟨r.original.length+(coefficients r.body).length,r.variables,targets r,
    guard r :: (bindings r ++ bodyRows r),0⟩

theorem request_original_prefix (r : Input) :
    (request r).targets.take r.original.length=r.original := by simp [request,targets]
theorem request_height (r : Input) : (request r).height=0 := rfl

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
