import Holant.Complexity.ClosedNetworkEncoding

/-! Deterministic original-record rewrite for balanced complementary unary
pins. Pin-zero is placed at ordered binary port zero and pin-one at port one.
All original edges, labels below s, and ordered non-pin ports are unchanged.
Validity and partition preservation are separate theorems, not assumptions
in this total raw-record algorithm. Defaults are present on arbitrary data. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsRaw
open Holant.Complexity

/-- Last two source labels are literal pin0 and pin1. -/
def sourceArity (s : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ := if i<s then a i else 1
/-- Last target label is the ordered rank-one 01 tensor. -/
def targetArity (s : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ := if i<s then a i else 2

def oldRows (s : ℕ) (r : RawClosedNetwork) : List RawVertex :=
  r.vertices.filter (fun row => row.1<s)

def pins (s : ℕ) (b : Bool) (r : RawClosedNetwork) : List RawEndpoint :=
  (r.vertices.filter (fun row => row.1=s+b.toNat)).flatMap Prod.snd

def pairedRow (s : ℕ) (r : RawClosedNetwork) (i : ℕ) : RawVertex :=
  (s,[(pins s false r).getD i (0,false),(pins s true r).getD i (0,false)])

def pairedRows (s : ℕ) (r : RawClosedNetwork) : List RawVertex :=
  (List.range (pins s false r).length).map (pairedRow s r)

def raw (s : ℕ) (r : RawClosedNetwork) : RawClosedNetwork where
  vertices := oldRows s r ++ pairedRows s r
  edges := r.edges

def Balanced (s : ℕ) (r : RawClosedNetwork) : Prop :=
  (pins s false r).length=(pins s true r).length

theorem edges_unchanged (s : ℕ) (r : RawClosedNetwork) : (raw s r).edges=r.edges := rfl

theorem pairedRows_length (s : ℕ) (r : RawClosedNetwork) :
    (pairedRows s r).length=(pins s false r).length := by
  simp [pairedRows]

theorem pairedRow_ports (s : ℕ) (r : RawClosedNetwork) (i : ℕ) :
    (pairedRow s r i).2.length=2 := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsRaw
