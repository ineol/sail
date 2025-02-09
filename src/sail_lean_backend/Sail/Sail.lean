import Std.Data.DHashMap
namespace Sail

section Regs

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/
inductive Error : Type where
  | Exit
  | Unreachable
  | Assertion (s : String)
open Error

structure SequentialState (RegisterType : Register → Type) where
  regs : Std.DHashMap Register RegisterType
  mem : Unit
  tags : Unit

inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)

abbrev PreSailM (RegisterType : Register → Type) :=
  EStateM Error (SequentialState RegisterType)

def writeReg (r : Register) (v : RegisterType r) : PreSailM RegisterType Unit :=
  modify fun s => { s with regs := s.regs.insert r v }

def readReg (r : Register) : PreSailM RegisterType (RegisterType r) := do
  let .some s := (← get).regs.get? r
    | throw Unreachable
  pure s

def readRegRef (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType α := do
  match reg_ref with | .Reg r => readReg r

def writeRegRef (reg_ref : @RegisterRef Register RegisterType α) (a : α) :
  PreSailM RegisterType Unit := do
  match reg_ref with | .Reg r => writeReg r a

def reg_deref (reg_ref : @RegisterRef Register RegisterType α) := readRegRef reg_ref

def vectorAccess [Inhabited α] (v : Vector α m) (n : Nat) := v[n]!

def assert (p : Bool) (s : String) : PreSailM RegisterType Unit := if p then pure () else throw (Assertion s)

end Regs

namespace BitVec

def length {w : Nat} (_ : BitVec w) : Nat := w

def signExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.signExtend w'

def zeroExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.zeroExtend w'

def truncate {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.truncate w'

def truncateLsb {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.extractLsb' (w - w') w'

def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb hi lo

def updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) : BitVec w :=
  let mask := ~~~(((BitVec.allOnes len).zeroExtend w) <<< start)
  let y' := mask ||| ((y.zeroExtend w) <<< start)
  x &&& y'

def updateSubrange {w : Nat} (x : BitVec w) (hi lo : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x lo _ y

def access {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[i]!

def addInt {w : Nat} (x : BitVec w) (i : Int) : BitVec w :=
  x + BitVec.ofInt w i

end BitVec

section concurrency_interface

inductive Access_variety where
| AV_plain
| AV_exclusive
| AV_atomic_rmw
open Access_variety (AV_plain AV_exclusive AV_atomic_rmw)

inductive Access_strength where
| AS_normal
| AS_rel_or_acq
| AS_acq_rcpc
export Access_strength(AS_normal AS_rel_or_acq AS_acq_rcpc)

structure Explicit_accessKind where
  variety : AccessVariety
  strength : AccessStrength

inductive Access_kind (arch : Type) where
  | AK_explicit (_ : Explicit_access_kind)
  | AK_ifetch (_ : Unit)
  | AK_ttw (_ : Unit)
  | AK_arch (_ : arch)
export Access_kind(AK_explicit AK_ifetch AK_ttw AK_arch)

structure Mem_read_request
  (k_n : Nat) (k_vasize : Nat) (k_pa : Type) (k_ts : Type) (k_arch_ak : Type) where
  access_kind : Access_kind k_arch_ak
  va : (Option (BitVec k_vasize))
  pa : k_pa
  translation : k_ts
  size : Int
  tag : Bool

structure Mem_write_request
  (k_n : Nat) (k_vasize : Nat) (k_pa : Type) (k_ts : Type) (k_arch_ak : Type) where
  access_kind : Access_kind k_arch_ak
  va : (Option (BitVec k_vasize))
  pa : k_pa
  translation : k_ts
  size : Int
  value : (Option (BitVec (8 * k_n)))
  tag : (Option Bool)

def sail_mem_write (req : Mem_write_request n vasize pa ts arch) :  PreSailM RegisterType (Result (Option Bool) A.abort) e

end concurrency_interface

end Sail
