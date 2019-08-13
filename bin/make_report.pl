#!/usr/bin/perl

#use HTML::FromANSIl
my ($URLBASE,$STAMP,$RESULTSDIR,$BENCHMARKS) = @ARGV;
my @bench = split ':', $BENCHMARKS;
my $MAXTREES = 2;

sub postprocesstree {
    my ($tree) = @_;
    $tree =~ s/write_headers\(\);/write_headers\(\);\\\\ /mg;
    $tree =~ s/([a-zA-Z])_([a-zA-Z])/$1\\_$2/mg;
    $tree =~ s/([a-zA-Z])_([a-zA-Z])/$1\\_$2/mg;
    $tree =~ s/send\(n\);/send(n);\\\\ /mg;
    $tree =~ s/sendA\(n\);/sendA(n);\\\\ /mg;
    $tree =~ s/(scanf\(\[^\)]+\);)/$1\\\\/mg;
    $tree =~ s/(\(\) = D\(\);)/$1\\\\/mg;
    $tree =~ s/shutdown\(\);/shutdown();\\\\ /mg;
    $tree =~ s/getchar\(\);/getchar();\\\\ /mg;
    $tree =~ s/err = copyout/\\\\err = copyout/mg;
    $tree =~ s/pingall\(\);/pingall();\\\\ /mg;
    $tree =~ s/(printf\([a-z0-9, ]+\);)/$1\\\\/mg;
    $tree =~ s/([a-zA-Z])_(\d+)/$1_{$2}/mg;
    return $tree;
}

open IDX, ">$RESULTSDIR/SUMMARY.html" or die $!;
open EM, ">$RESULTSDIR/EMAIL.txt" or die $!;
open TEX, ">$RESULTSDIR/RESULTS.tex" or die $!;
open FULL, ">$RESULTSDIR/FULLRESULTS.tex" or die $!;
open NBENCH, ">$RESULTSDIR/NUMBENCH.tex" or die $!;
#print FULL "\n\n\\begin{center}\\emph{(Begins on next page.)}\\end{center}\n";
#print FULL "\\begin{landscape}\n";
print EM "*** RESULTS OF RUNNING ALL BENCHMARKS ***\n";
print IDX "<html><head><style> table { width:100%; } table, th, td { border: 1px solid black; border-collapse: collapse; } th, td { padding: 15px; text-align: center; } tr:nth-child(even) { background-color: #eee; } tr:nth-child(odd) { background-color: #fff; } </style></head>";
print IDX "<body><h2>Benchmark Output</h2><table style=\"border: 1pt solid black;\">\n";
print IDX "<tr><th rowspan=\"2\">Benchmark</th><th rowspan=\"2\">Raw Output</th><th rowspan=\"2\">loc</th><th rowspan=\"2\">fs</th><th rowspan=\"2\">Dir</th><th rowspan=\"2\">Time (s)</th><th rowspan=\"2\">Sols</th><th colspan=\"2\">Tuples</th><th colspan=\"2\">Hypos</th></tr>\n";
print IDX "<tr><th>min</th><th>max</th><th>min</th><th>max</th></tr>\n";
#print TEX "\\setlength\\tabcolsep{1.2pt}\n";
print TEX "\\begin{tabular}{|r|l|r|r|c||r|r|c||r|r|r|r|}\n";
#mintuples maxtuples avgtuples minaxioms maxaxioms bestsolax bestsoltu
print TEX "\\hline\n\\rowcolor{lightgray}\n";
print TEX " & & & & & {\\bf Time} &  & {\\bf Exp./} & \\multicolumn{2}{|c|}{{\\bf Tuples}} & \\multicolumn{2}{|c|}{{\\bf Hypos.}} \\\\\n";
print TEX "\\rowcolor{lightgray}\n";
print TEX "{\\bf \\#} & {\\bf Benchmark} & {\\bf loc} & {\\bf Fns.} & {\\bf Dir} & {\\bf (s)} & {\\bf Sols.} & {\\bf Res.} & \\emph{min} & \\emph{max} & \\emph{min} & \\emph{max} \\\\\n";
print TEX "\\hline\n";
my $i = 0;
open VSLOC, ">$RESULTSDIR/VSLOC.csv" or die $!;
foreach my $b (sort @bench) {
    next if $b eq "";
    ++$i;
    my $Tim = qx{grep " Time: " $RESULTSDIR/kn-$b.txt};
    chomp($Tim); $Tim =~ s/^.*ime: (.*) \(s\).*$/$1/;
    my $Rs = qx{grep " Result " $RESULTSDIR/kn-$b.txt | wc -l};
    $Rs =~ s/[ \n]//g;
    my $SolStats = qx{grep "Solution Stats:" $RESULTSDIR/kn-$b.txt};
    my %digest;
    $digest{$_} = 0 for qw/mintuples maxtuples avgtuples minaxioms maxaxioms avgaxioms bestsolax bestsoltu/;
    if (0+$Rs > 0) {
	$digest{$_} = 99999 for qw/mintuples minaxioms/;
	foreach my $statsline (split /\n/, $SolStats) {
	    if ($statsline =~ /Size=(\d+), NAxioms=(\d+)$/) {
		$digest{mintuples} = $1 if $1 < $digest{mintuples};
		$digest{maxtuples} = $1 if $1 > $digest{maxtuples};
		$digest{avgtuples} += $1;
		$digest{minaxioms} = $2 if $2 < $digest{minaxioms};
		$digest{maxaxioms} = $2 if $2 > $digest{maxaxioms};
		$digest{avgaxioms} += $2;
		$digest{bestsolax} = $2 if ($digest{minaxioms} == $2);
		$digest{bestsoltu} = $1 if ($digest{minaxioms} == $2);
	    } else { die $statsline; }
	}
	$digest{avgtuples} = $digest{avgtuples} / (0 +  $Rs);
	$digest{avgaxioms} = $digest{avgaxioms} / (0 +  $Rs);
    }
    # Size=1, NAxioms=5

    my $stats = qx{grep " Statistics: " $RESULTSDIR/kn-$b.txt};
    $stats =~ s/^.* Statistics: \{(.*)\}\n$/$1/;
    my %stats_kv = map { split('=',$_) } split(',', $stats);
    my $expect = qx{grep "NO SOLUTION" bench/$b};
    $expect = ($expect eq '' ? '\\EVsome' : '\\EVnone');
    my $cmplt = qx{grep cmpLt bench/$b};
    my $cmpltIDX = ($cmplt eq '' ? '&equals;' : '&le;');
    $cmplt = ($cmplt eq '' ? '\\EVcmp' : '\\EVclt');
    #my $C1 = qx{grep "C1:" $RESULTSDIR/kn-$b.html};
    #my $C2 = qx{grep "C2:" $RESULTSDIR/kn-$b.html};
    # my $loc = qx{wc -l bench/$b | cut -c 1-8};
    my $loc = qx{wc -l < bench/$b};
    $loc =~ s/[ \n]//g;
    chomp($C1); chomp($C2);
    #print EM "$b : RESULT : $URLBASE/results-$STAMP/kn-$b.html\n";
    printf EM "  %-15s : %-4.3f : %4d : %-20s : (result here)\n", $b, $Tim, $Rs, $C2;
    print FULL "\\subsection{Example synthesized solution for benchmark \\texttt{$b}}\n";
    print FULL "\\begin{scriptsize}\n";
    #my $src = qx{cat bench/$b};
    #print FULL "\\begin{small}\\begin{verbatim}\n$src\n\n\\end{verbatim}\\end{small}\n";
    my $trees = qx{grep TEX $RESULTSDIR/kn-$b.txt | cut -c 6-};
    my $saved = ''; my $ct=0;
    for my $treeline (split /\n/, $trees) {
	++$ct if $treeline =~ /dirtree/;
	$saved .= "$treeline\n" if ($ct < $MAXTREES);
    }
    my $result = ($ct > 0 ? '\\EVsome' : '\\EVnone');
    if($result ne $expect) { $result = "\\red{$result}"; }
    printf TEX "%3d & %-15s & %4d & %4d & %6s & %4.2f &  %4d & %-5s / %-5s & %4d & %4d & %4d & %4d \\\\\n",
        $i, "\\texttt{$b}", $loc, $stats_kv{procs}, $cmplt, $Tim, $Rs, $expect, $result,
        map($digest{ $_}, qw/mintuples maxtuples minaxioms maxaxioms/);
    print IDX "<tr style=\"border-top: 1pt solid black;\"><td><pre>$b</pre><td><a href=\"kn-$b.html\">$b</a></td><td>$loc</td><td>$stats_kv{procs}</td><td>$cmpltIDX</td><td>$Tim</td><td>$Rs</td><td>$digest{mintuples}</td><td>$digest{maxtuples}</td><td>$digest{minaxioms}</td><td>$digest{maxaxioms}</td></tr>\n";

    print VSLOC "$loc;$Tim;$Rs\n";
    #print FULL "\\paragraph{Solutions generated by {\\knotical}} \$\\;\$\n";
    #print FULL "\\[\\begin{array}{l}\n$trees\n\\end{array}\\]\n";
    print FULL postprocesstree($saved)."\n";
    print FULL "\\end{scriptsize}\n";
    if ($ct == 0) { print FULL "\\medskip\n\\emph{No solutions.}\n"; }
    if ($ct > $MAXTREES) { print FULL "\\medskip\n\\emph{Remaining ".($ct-$MAXTREES)." solutions ommitted for brevity.}\n"; }
    #%foreach my $ln (split /\n/, $trees)
}
close VSLOC;
print IDX "</ul></body></html>\n";
close IDX;
close EM;
my $count = 0 + @bench;
print NBENCH "\\newcommand\\numbenchmarks{$count}\n";
close NBENCH;
#print TEX "\\hline\n\\hline\n";
#printf TEX "%3d & {\bf Totals:} & %4d & %4d & %6s & %4.2f &  %4d & %-5s & %-5s \\\\\n",
#	$count, $loc, $stats_kv{procs}, $cmplt, $Tim, $Rs, $expect, $result;
print TEX "\\hline\n";
print TEX "\\end{tabular}\n";
close TEX;
#print FULL "\\end{landscape}\n";
close FULL;
