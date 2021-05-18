#! /bin/sh

# Copyright 2013-2017 IBM Corp.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# 	http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

run_binary() {
	if [ -x "$1" ] ; then
		$VALGRIND "$1" $2 2>> $STDERR_OUT 1>> $STDOUT_OUT
	else
		echo "Fatal error, cannot execute binary '$1'. Did you make?";
		exit 1;
	fi
}

fail_test() {
	echo "$0 ($CUR_TEST): test failed";
	echo "Test directory preserved:"
	echo "  DATA_DIR = $DATA_DIR"
	echo "  STDOUT = $STDOUT_OUT"
	echo "  STDERR = $STDERR_OUT"
	exit ${1:-1};
}

pass_test() {
	/bin/true;
}

strip_version_from_result() {
	VERSION=$(./make_version.sh $1)
	sed -i "s/${VERSION}/VERSION/;s/^Open-Power \(.*\) tool .*/Open-Power \\1 tool VERSION/" $STDERR_OUT
	sed -i "s/${VERSION}/VERSION/;s/^Open-Power \(.*\) tool .*/Open-Power \\1 tool VERSION/" $STDOUT_OUT
}

diff_with_result() {
	# Explicitly diff a file with an arbitrary result file
	if [ "$#" -eq 1 ] ; then
		if ! diff -u "$RESULT" "$1" ; then
			fail_test;
		fi
	# Otherwise just diff result.out with stdout and result.err with stderr
	else
		#Strip carriage returns, useful for pflash which does fancy
		#'progress bars'. The main reason for this is is that email
		#doesn't barf at really really long lines
		if ! cat "$STDOUT_OUT" | tr '\r' '\n' | \
			diff -u	"${RESULT}.out" - ; then
			fail_test;
		fi
		if ! cat "$STDERR_OUT" | tr '\r' '\n' | \
			diff -u "${RESULT}.err" - ; then
			fail_test;
		fi
	fi
}

run_tests() {
	if [ $# -lt 2 ] ; then
		echo "Usage run_tests test_dir result_dir [data_dir]";
		exit 1;
	fi

	all_tests="$1";
	res_path="$2";

	if [ ! -d "$res_path" ] ; then
		echo "Result path isn't a valid directory";
		exit 1;
	fi

	export DATA_DIR=$(mktemp --tmpdir -d external-test-datadir.XXXXXX);
	export STDERR_OUT="$DATA_DIR/stderr"
	export STDOUT_OUT="$DATA_DIR/stdout"
	if [ $# -eq 3 ] ; then
		cp -r $3/* "$DATA_DIR"
	fi


	for the_test in $all_tests; do
		export CUR_TEST=$(basename $the_test)
		export RESULT="$res_path/$CUR_TEST"
		echo "running $the_test"

		. "$the_test";
		R="$?"
		if [ "$R" -ne 0 ] ; then
			fail_test "$R";
		fi
	#reset for next test
	> "$STDERR_OUT";
	> "$STDOUT_OUT";
	done

	rm -rf $STDERR_OUT;
	rm -rf $STDOUT_OUT;
	rm -rf $DATA_DIR;

	echo "$0 tests passed"

	exit 0;
}

