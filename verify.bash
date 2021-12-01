#!/bin/bash

REPO=`pwd`
OJ=./openjml
SRC_PATH=$REPO/Demo/toy_example
JML_PATH=$REPO/Demo/jml

echo "Performing Type checking..."
echo "java -jar $OJ/openjml.jar $SRC_PATH/Student.java -specspath $JML_PATH"
java -jar $OJ/openjml.jar $SRC_PATH/Student.java -specspath $JML_PATH

echo "Performing Static verification..."
echo "java -jar $OJ/openjml.jar -esc $SRC_PATH/Student.java -specspath $JML_PATH -exec $OJ/Solvers-macos/z3-4.5.0"
java -jar $OJ/openjml.jar -esc $SRC_PATH/Student.java -specspath $JML_PATH -exec $OJ/Solvers-macos/z3-4.5.0

echo "Performing Runtime Assertion checking..."
echo "java -jar $OJ/openjml.jar -rac $SRC_PATH/Student.java -specspath $JML_PATH"
java -jar $OJ/openjml.jar -rac $SRC_PATH/Student.java -specspath $JML_PATH
echo "java -classpath "$SRC_PATH:$OJ/jmlruntime.jar Student""
java -classpath "$SRC_PATH:$OJ/jmlruntime.jar" Student 
