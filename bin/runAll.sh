#!/bin/bash

timeout=10
interval=2
delay=5
set -x
# find root project path from this script path
#dir=$(realpath -L $(dirname $0)/../)
bindir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
URLBASE="file://$bindir/.."

# benchmarks
cd $bindir/../bench
EXAMPLES=$(ls *.c) # 00*.c 01*.c 02*.c) # 01sendrecv.c)

export STAMP=`date +'%Y%m%d-%H%M%S'`
export RESULTSDIR=$bindir/../results-$STAMP

#################################
# Run the benchamrks
cd $bindir/../
mkdir -p $RESULTSDIR
chmod 755 $RESULTSDIR
chmod +x $bindir/ansi2html.sh

EXS=""
cd $bindir/../
for ex in $EXAMPLES; do
    EXS=$ex:$EXS
    echo "$EXS"
    grep 'ARGS' bench/$ex
    if [ $? -eq 0 ]; then 
	ARGS=$(grep ARGS bench/$ex | cut -c 9-)
    else
	ARGS="-cmp C1 C2 -tex"
    fi
    echo "ARGS: $ARGS";
    time ./knotical.native bench/$ex $ARGS 2>&1 >$RESULTSDIR/kn-$ex.txt
    cat $RESULTSDIR/kn-$ex.txt | $bindir/ansi2html.sh > $RESULTSDIR/kn-$ex.html
    # (
    # 	echo -n "waiting for [$ex] "
    # 	((t = timeout))
    # 	while ((t > 0)); do
    #         sleep $interval
    # 	    echo -n "."
    #         kill -0 $$ || exit 0
    #         ((t -= interval))
    # 	done
    # 	echo "\n"
    # 	# 'exit 0' will be executed if any preceeding command fails.
    # 	kill -s SIGTERM $$ && kill -0 $$ || exit 0
    # 	sleep $delay
    # 	kill -s SIGKILL $$
    # ) 2> /dev/null &
    # exec time ./knotical.native bench/$ex -cmp 'C1' 'C2' 2>&1 | $bindir/ansi2html.sh > $RESULTSDIR/kn-$ex.html
done

#################################
# Generate report
chmod +x $bindir/make_report.pl
$bindir/make_report.pl $URLBASE $STAMP $RESULTSDIR $EXS

set +x
echo ""
echo ""
echo ""
# cat $RESULTSDIR/EMAIL.txt
# cat $RESULTSDIR/RESULTS.tex
echo ""
echo "Result saved to: $RESULTSDIR/SUMMARY.html"
echo ""
