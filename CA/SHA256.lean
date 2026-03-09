namespace CA.SHA256

/-- Compute SHA-256 hash of a ByteArray, returning 32 bytes. -/
@[extern "lean_sha256_hash"]
opaque sha256 (data : @& ByteArray) : IO ByteArray

private def hexDigit (n : UInt8) : Char :=
  let n := n.toNat
  if n < 10 then Char.ofNat (n + 48)
  else Char.ofNat (n - 10 + 97)

/-- Convert a 32-byte ByteArray to a 64-character hex string. -/
def toHex256 (bytes : ByteArray) : String := Id.run do
  let mut chars : Array Char := Array.mkEmpty (bytes.size * 2)
  for i in [:bytes.size] do
    let b := bytes.get! i
    chars := chars.push (hexDigit (b >>> 4))
    chars := chars.push (hexDigit (b &&& 0x0F))
  return String.ofList chars.toList

end CA.SHA256
