.PHONY: all

all: carmada

carmada: carmada.cpp
	clang++ -ggdb -std=c++17 carmada.cpp -o carmada -lLLVM-9 -lclangBasic -lclangAST -lclangSerialization -lclangFrontend -lclangTooling
