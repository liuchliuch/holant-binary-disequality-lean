import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCertificate
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinRMPhaseSupport

/-! Exact integral finite domain for the standard six-port Bell source.
The first Bell card is fixed to I tensor I; the three other matching cards
retain all labels and signs. No certificate conclusion is assumed here. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixFiniteData
open Holant
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
def positive : Fin 48→ℕ := ![36873,24582,4097,8194,2448,1632,272,544,9,6,32769,16386,144,96,2064,1056,33825,18450,1025,2050,8580,4680,260,520,33,18,32769,16386,132,72,8196,4104,33345,10260,513,2052,16770,5160,258,1032,65,20,32769,8196,130,40,16386,4104]
def negative : Fin 48→ℕ := ![0,0,32776,16388,0,0,2176,1088,36864,24576,4104,8196,2304,1536,384,576,0,0,32800,16400,0,0,8320,4160,33792,18432,1056,2064,8448,4608,384,576,0,0,32832,8208,0,0,16512,4128,33280,10240,576,2064,16640,5120,384,1056]
def orthogonalMask : Fin 48→ℕ := ![136195491168254,202231620960253,244623595012091,261374223056887,202231620960239,136195491168223,261374223056831,244623595011967,244623595011839,261374223056383,136195491167231,202231620958207,261374223052799,244623595003903,202231620943871,136195491135487,136197707824094,202232829949933,244624157040251,261374529236407,202232829032429,136197705792478,261374525566391,244624148913787,244624140525179,261374496206263,136197640780766,202232695863277,261374261325239,244623620431483,202231756339181,136195560405982,281468464954334,281465177618413,281457234534011,281440310259127,281405048076269,281335320968158,281199792090551,280924658589307,280374902775419,279275646741943,277074713410526,272677674530797,263882483953079,246290042314363,211105023375341,140735271566302]
def supportMasks : Fin 12→ℕ := ![1632,2448,4680,5160,8580,10260,16770,18450,24582,33345,33825,36873]
def positions : Fin 12→Fin 4→Fin 16 := ![![5,6,9,10],![4,7,8,11],![3,6,9,12],![3,5,10,12],![2,7,8,13],![2,4,11,13],![1,7,8,14],![1,4,11,14],![1,2,13,14],![0,6,9,15],![0,5,10,15],![0,3,12,15]]
def fill : Fin 4→Fin 16→Fin 4→Fin 64 := ![![![0,8,32,40],![1,9,33,41],![2,10,34,42],![3,11,35,43],![4,12,36,44],![5,13,37,45],![6,14,38,46],![7,15,39,47],![16,24,48,56],![17,25,49,57],![18,26,50,58],![19,27,51,59],![20,28,52,60],![21,29,53,61],![22,30,54,62],![23,31,55,63]],
  ![![0,4,32,36],![1,5,33,37],![2,6,34,38],![3,7,35,39],![8,12,40,44],![9,13,41,45],![10,14,42,46],![11,15,43,47],![16,20,48,52],![17,21,49,53],![18,22,50,54],![19,23,51,55],![24,28,56,60],![25,29,57,61],![26,30,58,62],![27,31,59,63]],
  ![![0,2,32,34],![1,3,33,35],![4,6,36,38],![5,7,37,39],![8,10,40,42],![9,11,41,43],![12,14,44,46],![13,15,45,47],![16,18,48,50],![17,19,49,51],![20,22,52,54],![21,23,53,55],![24,26,56,58],![25,27,57,59],![28,30,60,62],![29,31,61,63]],
  ![![0,1,32,33],![2,3,34,35],![4,5,36,37],![6,7,38,39],![8,9,40,41],![10,11,42,43],![12,13,44,45],![14,15,46,47],![16,17,48,49],![18,19,50,51],![20,21,52,53],![22,23,54,55],![24,25,56,57],![26,27,58,59],![28,29,60,61],![30,31,62,63]]]

def line (a : Fin 48) (i : Fin 16) : ℤ :=
  if (positive a).testBit i.val then 1 else if (negative a).testBit i.val then -1 else 0

def orthogonal (a b : Fin 48) : Bool := (orthogonalMask a).testBit b.val

def sign (s : Fin 8) (k : ℕ) : ℤ := if s.val.testBit k then -1 else 1

def source (a b c : Fin 48) (s : Fin 8) (w : Fin 64) : ℤ :=
  let i : Fin 16 := ⟨w.val%16,Nat.mod_lt _ (by decide)⟩
  if w.val<16 then line 0 i+sign s 1*line b i
  else if w.val<32 then sign s 0*line a i+sign s 2*line c i
  else if w.val<48 then sign s 0*line a i-sign s 2*line c i
  else line 0 i-sign s 1*line b i

def card (a b c : Fin 48) (s : Fin 8) (j k : Fin 4) (x : Fin 16) : ℤ :=
  ∑t : Fin 4,GlobalCloseCompletionKleinGramCertificate.pauli k
    (GlobalCloseCompletionKleinGramCertificate.word t 0)
    (GlobalCloseCompletionKleinGramCertificate.word t 1)*source a b c s (fill j x t)

def supportMask (q : Fin 16→ℤ) : ℕ := ∑i : Fin 16,if q i=0 then 0 else 2^i.val

def fourSafe (q : Fin 16→ℤ) (p : Fin 12) : Bool :=
  let a := q (positions p 0)
  let b := q (positions p 1)
  let c := q (positions p 2)
  let d := q (positions p 3)
  decide (a^2=b^2 ∧ a^2=c^2 ∧ a^2=d^2 ∧ 0<a*b*c*d)

def safe (q : Fin 16→ℤ) : Bool :=
  let m := supportMask q
  (m==0) || decide (∃p : Fin 12,m=supportMasks p ∧ fourSafe q p=true)

def accepted (a b c : Fin 48) (s : Fin 8) : Bool :=
  orthogonal 0 a && orthogonal 0 b && orthogonal 0 c &&
  orthogonal a b && orthogonal a c && orthogonal b c &&
  decide (∀j k : Fin 4,safe (card a b c s j k)=true)

def allowed (a b c : Fin 48) : Prop :=
  (a=1 ∧ b=2 ∧ c=3) ∨ (a=4 ∧ b=8 ∧ c=12) ∨
  (a=11 ∧ b=13 ∧ c=6) ∨ (a=14 ∧ b=7 ∧ c=9)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixFiniteData
