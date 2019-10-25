load "HFE-_generate_keys.m";

invert_phi := function(vector,l)
  if Type(vector) eq SeqEnum then
    sum := &+ [vector[k]*a^(k-1) : k in [1..#vector]];
    if l gt #vector then
      sum +:= &+ [Random(F2)*a^(k-1) : k in [1..(l-#vector)]];
    end if;
    return sum;
  else
    sum := 0;
    for k in [1..l] do
      try
        sum +:= vector[k][1]*a^(k-1);
      catch e
        sum +:= Random(F2)*a^(k-1);
      end try;
    end for;
    return sum;
  end if;
end function;

phi := function(Z,l) // Z is in MPF2n
  canon := F2n_to_PF2(Z);  // expressed as a polynom with b coefficients in the canonical base.
  vect_Z := Matrix(F2,l,1,[0 : k in [1..l]]);
  for i in [1..#Coefficients(canon)] do
    vect_Z[i][1] := Coefficients(canon)[i];
  end for;
  return vect_Z;
end function;

cipher := function(message, public_key)
  not_pol_ring := Evaluate(public_key, message);
  return Matrix(F2,m,1,[not_pol_ring[k] : k in [1..m]]);
end function;

apply_F := function(message,univF) // you still need to reduce the dimension after that.
  MPF2n_message := invert_phi(message, n); // = &+ [message[k]*a^(k-1) : k in [1..n]];
  return Evaluate(univF,MPF2n_message);
end function;

invert := function(d, univF, S, T, n, m)
  // T^(-1)*d; // incompatible coefficient rings
  roots := [];
  while #roots eq 0 do
    MPF2n_invT_d := invert_phi(Matrix(F2,m,1,[&+[d[i]*(T^(-1))[k,i] : i in [1..m]] : k in [1..m]]), n);
    roots := Roots(univF-MPF2n_invT_d);
  end while;
  r := Random(1,#roots);  // maybe we should give more weight to roots with higher multiplicity? -> TODO
  vect_r := phi(roots[r][1],n);  // vertical matrix in F2;
  return Matrix(F2,n,1,[&+[vect_r[i][1]*(S^(-1))[k,i] : i in [1..n]] : k in [1..n]]);
end function;

sign := function(message, univF, S, T, n, m)
  H := Intseq(Hash(message),2);
  Si := Matrix(F2,n,1,[0 : k in [1..n]]);
  found_inverse := false;
  iter := 1;
  while found_inverse eq false do
    D := Matrix(F2,n,1,[H[k] : k in [1..n]]);
    DxorSi := D + Si;    // addition in F2 is a xor operation.
    try
      Si := invert(DxorSi, univF, S, T, n, m);
      found_inverse := true;
    catch e
      print Transpose(DxorSi), " n'est pas inversible.";
      iter +:= 1;
    end try;
    H := Intseq(Hash(H),2);
  end while;
  return Si, iter;
end function;

check_signature := function(signature, message, public_key, nb_ite, m)
  H := Intseq(Hash(message),2);
  Si := signature;
  // D := Matrix(F2, nb_ite, n, [0 : k in [1..n*nb_ite]]);
  for i in [1..(nb_ite-1)] do
    // D[i] := Vector(F2,[H[k] : k in [1..n]]);
    H := Intseq(Hash(H),2);
  end for;
  D := Matrix(F2,m,1,[H[k] : k in [1..m]]);
  // for i in [(nb_ite-1)..0] do
  //   Si := Matrix(F2,n,1,[Evaluate(public_key, [Si[k]: k in [1..n]])[k] : k in [1..n]]) + D[i];
  // end for;
  Si := Matrix(F2,m,1,[Evaluate(public_key, [Si[l][1]: l in [1..n]])[k] : k in [1..m]]) + D;
  if Si eq Matrix(F2,m,1,[0 : k in [1..m]]) then
    return "La signature est valide.";
  else
    return "La signature n'est pas valide.";
  end if;
end function;

message := [Random(F2) : k in [1..n]];  // is a list
print("Message : ");
Matrix(F2,1,n,message);
cipher_m := cipher(message, public_key);  // is a vertical matrix
print("Message chiffré : ");
Transpose(cipher_m);

// MPF2n_cipher_m := &+ [cipher_m[k]*a^(k-1) : k in [1..n]];
// MPF2n_cipher_m;

// fed_m := apply_F(message, univF);
// Roots(univF-fed_m);

inverted_cipher_m := invert(cipher_m, univF, S, T, n, m);
print("Inverse du message chiffré : ");
Transpose(inverted_cipher_m);

// verification :
print("Chiffrement de l'inverse du message chiffré : ");
Transpose(cipher([inverted_cipher_m[k][1] : k in [1..n]], public_key));

// nb_ite := 4;
m_signature, m_sign_iters := sign(message, univF, S, T, n, m);
if m_sign_iters eq 1 then
  print "signature du message, en 1 itération : ";
else
  print "signature du message, en ", m_sign_iters, " itérations : ";
end if;
Transpose(m_signature);

// Signature verification :
verif := check_signature(m_signature, message, public_key, m_sign_iters, m);
print verif;
