#!/bin/bash

REPO_PATH=.
DEMO_PATH=$REPO_PATH/Demo
TOOL_PATH=.
GRAM_PATH=$TOOL_PATH/grammar
PY="python3.9"

GRAM_FILE=$GRAM_PATH/simple_grammar.fcfg
DOC_FILE=$DEMO_PATH/build/xml/class_student.xml
JML_FILE=$DEMO_PATH/jml/student.jml


if ! [ -x "$(command -v python3.9)" ] && ! [ -x "$(command -v python3)" ] && ! [ -x "$(command -v python)" ];
then
    echo "Error: You need python with version 3.9 or above to run the tool"
    exit 1
else
	if [ -x "$(command -v python3.9)" ]
	then
		echo "User python3.9 as command..."
		PY="python3.9"
	elif [ -x "$(command -v python3)" ];
    	then
        	echo "Use python3 as command..."
        	PY="python3"
	else
		echo "There are no python3 and python3.9, I assume you are using python with version 3.9."
		echo "Try to use python as command..."
		PY="python"
    	fi
fi

echo "Checking the Demo folder..."
if [[ -d "$DEMO_PATH/build" ]]
then
    echo "Demo build folder exists...cleaning up"
    rm -rf "$DEMO_PATH/build/*"
else
    echo "Creating the build folder..."
    mkdir "$DEMO_PATH/build"
fi

if [[ -d "$DEMO_PATH/jml" ]]
then
    echo "JML folder exists...cleaning up"
    rm -rf "$DEMO_PATH/jml/*"
else
    mkdir "$DEMO_PATH/jml"
fi

echo "Generating the documentation..."
cd "$DEMO_PATH/toy_example"
doxygen

cd ../../
#echo "$PY main.py -i $DOC_FILE -o $JML_FILE -g $GRAM_FILE" 
echo "Running the Natural language to Contract Translator..."
${PY} main.py -i $DOC_FILE -o $JML_FILE -g $GRAM_FILE

