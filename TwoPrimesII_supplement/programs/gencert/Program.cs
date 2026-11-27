// Writes the certificate matrix as Lean data, with an inverse modulo 2.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Text.Json;

using var doc = JsonDocument.Parse(File.ReadAllText(args[0]), new JsonDocumentOptions { MaxDepth = 64 });
var root = doc.RootElement;
BigInteger Big(JsonElement e) => BigInteger.Parse(e.ValueKind == JsonValueKind.String ? e.GetString() : e.GetRawText());
var sel = root.GetProperty("selected_digits").EnumerateArray()
    .Select(e => (prime: (int)Big(e.GetProperty("prime")), j: (int)Big(e.GetProperty("j")))).ToList();
var B = root.GetProperty("basis").EnumerateArray().Select(r => r.EnumerateArray().Select(Big).ToArray()).ToArray();
int h = sel.Count;
if (h != 124 || B.Length != h || B.Any(r => r.Length != h)) throw new Exception("shape");

// inverse of B over GF(2)
var M = new BigInteger[h];
var I = new BigInteger[h];
for (int i = 0; i < h; i++)
{
    for (int j = 0; j < h; j++) if (!B[i][j].IsEven) M[i] |= BigInteger.One << j;
    I[i] = BigInteger.One << i;
}
for (int c = 0; c < h; c++)
{
    int piv = -1;
    for (int r = c; r < h; r++) if (!(M[r] >> c).IsEven) { piv = r; break; }
    if (piv < 0) throw new Exception("singular modulo 2");
    (M[c], M[piv]) = (M[piv], M[c]);
    (I[c], I[piv]) = (I[piv], I[c]);
    for (int r = 0; r < h; r++)
        if (r != c && !(M[r] >> c).IsEven) { M[r] ^= M[c]; I[r] ^= I[c]; }
}

var o = new StringBuilder();
o.Append("/-! Data of the 124-dimensional certificate: the matrix by rows, the primes and the digit\nnumbers of the 124 chosen digits, and an inverse of the matrix modulo 2 (row `j` as a bit mask).\nGenerated from the public file in `TwoPrimes_supplement/basis124`. -/\n\n");
o.Append("namespace TwoPrimesBasisData\n\n");
for (int i = 0; i < h; i++)
    o.Append($"def r{i} : List Int := [{string.Join(", ", B[i].Select(x => x.ToString()))}]\n");
o.Append("\ndef rows : List (List Int) := [" + string.Join(", ", Enumerable.Range(0, h).Select(i => "r" + i)) + "]\n\n");
o.Append("def bases : List Nat := [" + string.Join(", ", sel.Select(x => x.prime.ToString())) + "]\n\n");
o.Append("def digits : List Nat := [" + string.Join(", ", sel.Select(x => x.j.ToString())) + "]\n\n");
o.Append("def inv2 : List Nat := [" + string.Join(", ", I.Select(x => x.ToString())) + "]\n\n");
o.Append("def widths : List Nat := [" + string.Join(", ", Enumerable.Range(0, h).Select(j => B.Aggregate(BigInteger.Zero, (a, r) => a + BigInteger.Abs(r[j])).ToString())) + "]\n\n");
o.Append("end TwoPrimesBasisData\n");
File.WriteAllText(args[1], o.ToString(), new UTF8Encoding(false));
Console.WriteLine($"h={h} bases: {sel.Count(x => x.prime == 2)} of 2, {sel.Count(x => x.prime == 3)} of 3; first {sel[0]} last {sel[h - 1]}");
