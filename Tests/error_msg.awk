BEGIN { g=0; }
NF==0 { next; }
$1 == "***" && $2 == "Garbage" { g=g+1; }
$1 == "***" && $2 != "Garbage" {
	if (g!=0) printf "*** Garbage Collections: %d\n", g;
	g=0;
	print $0
}
$1 != "***" { 
	if (g!=0) printf "*** Garbage Collections: %d\n", g;
	g=0;
	print $8
}

