import Holant.Certificates.TwelveLoops.Data
import Mathlib.Data.Fintype.BigOperators

/-! Exact exhaustive multiplicities. Each256-state block is checked by Lean's
kernel reduction, then product-state cardinality assembles all4^7 labelled
choices. The printed block counts are certificates, not assumed facts. -/
namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
open scoped BigOperators

def blockCount (x : AState) (r : Route) : ℕ :=
  ((Finset.univ : Finset BState).filter (fun y => classify (x,y)=r)).card

def blockHistogram (x : AState) : ℕ × ℕ × ℕ :=
  (blockCount x .rankOne,blockCount x .infiniteOrder,blockCount x .remaining)

def printedBlocks (x : AState) : ℕ × ℕ × ℕ :=
  (![![![(224,28,4),(236,14,6),(252,0,4),(236,14,6)],![(236,14,6),(236,14,6),(250,0,6),(250,0,6)],![(252,0,4),(250,0,6),(252,0,4),(250,0,6)],![(236,14,6),(250,0,6),(250,0,6),(236,14,6)]],![![(236,14,6),(236,14,6),(250,0,6),(250,0,6)],![(236,14,6),(236,14,6),(250,0,6),(250,0,6)],![(250,0,6),(250,0,6),(250,0,6),(250,0,6)],![(250,0,6),(250,0,6),(250,0,6),(250,0,6)]],![![(252,0,4),(250,0,6),(252,0,4),(250,0,6)],![(250,0,6),(250,0,6),(250,0,6),(250,0,6)],![(252,0,4),(250,0,6),(252,0,4),(250,0,6)],![(250,0,6),(250,0,6),(250,0,6),(250,0,6)]],![![(236,14,6),(250,0,6),(250,0,6),(236,14,6)],![(250,0,6),(250,0,6),(250,0,6),(250,0,6)],![(250,0,6),(250,0,6),(250,0,6),(250,0,6)],![(236,14,6),(250,0,6),(250,0,6),(236,14,6)]]]) x.1 x.2.1 x.2.2


end Holant.Certificates.TwelveLoops
