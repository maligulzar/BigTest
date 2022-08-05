# BigTest: White-Box Testing of Big Data Analytics with Complex User-Defined Functions

## Summary of BigTest 
Data-intensive scalable computing (DISC) systems such as Google’s MapReduce, Apache Hadoop, and Apache Spark are being leveraged to process massive quantities of data in the cloud. Modern DISC applications pose new challenges in exhaustive, automatic testing because they consist of dataflow operators, and complex user-defined functions (UDF) are prevalent unlike SQL queries. We design a new white-box testing approach, called BigTest to reason about the internal semantics of UDFs in tandem with the equivalence classes created by each dataflow and relational operator. Our evaluation shows that, despite ultra-large scale input data size, real world DISC applications are often significantly skewed and inadequate in terms of test coverage, leaving 34% of Joint Dataflow and UDF (JDU) paths untested. BigTest shows the potential to minimize data size for local testing by 10^5 to 10^8 orders of magnitude while revealing 2X more manually-injected faults than the previous approach. Our experiment shows that only few of the data records (order of tens) are actually required to achieve the same JDU coverage as the entire production data. The reduction in test data also provides CPU time saving of 194X on average, demonstrating that interactive and fast local testing is feasible for big data analytics, obviating the need to test applications on huge production data.

## Team 
If you encounter any problems, please open an issue or feel free to contact us:

[Muhammad Ali Gulzar](https://people.cs.vt.edu/~gulzar/):  Assistant Professor at Virginia Tech, gulzar@cs.vt.edu;

[Shaghayegh Mardani](https://github.com/ShaghayeghMrdn): PhD student;

[Madan Musuvathi](https://www.microsoft.com/en-us/research/people/madanm/): Partner Research Manager at Microsoft Research  

[Miryung Kim](http://web.cs.ucla.edu/~miryung/): Professor at UCLA, miryung@cs.ucla.edu;

## How to cite 
Please refer to our FSE'19 paper, [White-box testing of big data analytics with complex user-defined functions](https://people.cs.vt.edu/~gulzar/assets/pdf/fse2019-bigtest.pdf) for more details. 

### Bibtex  
@inproceedings{10.1145/3338906.3338953,
author = {Gulzar, Muhammad Ali and Mardani, Shaghayegh and Musuvathi, Madanlal and Kim, Miryung},
title = {White-Box Testing of Big Data Analytics with Complex User-Defined Functions},
year = {2019},
isbn = {9781450355728},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3338906.3338953},
doi = {10.1145/3338906.3338953},
booktitle = {Proceedings of the 2019 27th ACM Joint Meeting on European Software Engineering Conference and Symposium on the Foundations of Software Engineering},
pages = {290–301},
numpages = {12},
keywords = {test generation, map reduce, data intensive scalable computing, symbolic execution, dataflow programs},
location = {Tallinn, Estonia},
series = {ESEC/FSE 2019}
}

[DOI Link](https://doi.org/10.1145/3338906.3338953)

### Video 
You can find our demonstration video [here](https://doi.org/10.1145/3338906.3338953)
### Directory Structure:
* **BenchmarkFault** --> Contains the source code of both origianl and faulty benchmark programs
* **SymexScala** --> *The core of BigTest that contains the implementation of following components:*
    - Symbolic execution of UDF
    - Programmatic representation of logical specifications
    - UDF and Dataflow integration
    - Optimzation of SMT query and Invocatoin of theorem solvers
* **UdfExtractor** --> *Contains the implementation of transforming Scala code into Java and then extracting each UDF into a seperate class*
* **jpf-core and jpf-symbc** --> *Contains custom version of JPF and SPF*
* **fse_bigtest_2019.pdf** --> *The final version BigTest paper*

### Running benchmarks on pre-generated Test using BigTest:
 - Run TestSuiteRunner.scala under BenchmarkFault with dependency on Spark 2.1.0
 - To run applciations on original dataset, orignal datasets can be acquired from [PUMA](https://engineering.purdue.edu/~puma/datasets.htm) and data generation [scripts](https://github.com/maligulzar/BigTest/tree/JPF-integrated/BenchmarksFault/src/datagen)
 - A sample bigtest running log is available [here](https://github.com/maligulzar/BigTest/blob/JPF-integrated/BenchmarksFault/src/gradeanalysis/bigtest_gradanalysis.log) and a sample pathcondition SMT query is available [here](https://github.com/maligulzar/BigTest/blob/JPF-integrated/BenchmarksFault/src/gradeanalysis/pathcondition3.smt) 
 
 # Run End-to-End BigTest 
 
### Download latest version of Scala-IDE (this was tested on eclipse 4.7.1)
    Import 4 projects (jpf-core, jpf-symbc, udfextractor, symexScala) into eclipse using Java/Scala project (use source as working directory). Eclipse might not load the libraries under /lib folder. If that happens, manually load the jars using Eclipse project preferences menue. 
    At the end of this step, you should have 4 projects loaded into Eclipse. These steps are explained individual below. 
        
### Download z3 repo in base project dir
        https://github.com/Z3Prover/z3
        https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang
        Also set up python bindings
            https://github.com/Z3Prover/z3#python
### Install cvc4:
         Download Cvc4 [here](http://cvc4.cs.stanford.edu/downloads/)
        
### UDFExtractor:
        mkdir UDFExtractor/lib and unzip the 2nd archive folder there (jars)
        Project properties (UDFExtractor -> Java Build Path -> Libraries, add lib folder)
            remove the existing jar files (almost all current libraries)
            add new lib folder jars as external jars (it's mostly to fix up the jar paths)
### SymExec:
        Project properties (SymExec -> Java Build Path -> Libraries, add lib folder)
            remove the existing jar files (almost all current libraries)
            Add external library: jpf-symbc/build/*.jar (three jars: jpf-symbc{,-annotations,-classes})
            Add external library: jpf-core/build/RunJPF.jar
            --> 4 jars total
        Edit SymbolicResult -> remove "import sun.misc.ObjectInputFilter.Config" (not needed)
        "Examples" folder -> Mark as not source (no need to compile)
         alternate : comment out the two scala files
### jpf-symbc:
        Project properties (SymExec -> Java Build Path -> Libraries, add lib folder)
            remove the existing jar files (almost all current libraries)
            Add all jars in jpf-symbc/lib
### jpf-core:
        create site.properties in .jpf/"" according to https://github.com/javapathfinder/jpf-core/wiki/Creating-site-properties-file
        UDFExtractor -> right click -> Export -> Jar 
            uncheck all files (click the folder name) and expand dropdown -> only select "src" (no lib)
            Also select only the "src" folder or symexec
            Jar file name: jpf-core/lib/sym.jar
  
  
### Note: 
    BigTest has cyclic dependency i.e. SymexScala depends on original (not our custome) jpf-symbc's jar and jpf-core's jar. If you face dependency issues, compiled both udfextractor and symexScala using  original jpf from [JavaPathFinder](https://github.com/javapathfinder/jpf-core). To summarize, 
    1. Get jars files of original JPF-core and JPF-symbc
    2. Compile UDFExtractor and then SymexScala (symexscala depends on jar of udfextactor)
    3. Compiled Jpf-core and Jpf-symbc using SymexScala's and udfextractors's jar.

  
 ### Run: 
        Configurations -> Java Applications -> run-JPF-symbc (change VM argument for java lib path)
        Uncomment Test2.scala (from SymExec)
        You may need to re-export symex + udfextractor (uncomment the examples dir if so)
            do this for both jpf-core and jpf-symbc
        Update JPF.java (jpf-core)
        ignore warnings when launching
        To run your own DISC application two things are required:
            - Applications in scala 
            - JPF configuration file 
        Each benchmark contains a comment at the end of the file that has a JPF configuration. 
        To run BigTest, follow the procedue to run JPFCore and append the following cmd arguemnts *-enableBT <filename>*
        JPF will automatically look for filename.class and filename.JPF
### Path fixes required: find and replace "up_jpf" -> "Test-..." (Soon to be fixed)
     Peform a text search on the whole repository to update paths:
    - check for malig on path. Especially, Configuration and SystemCommandHandler
    - also check for amytis
    - SymbolicResult: line 74ish, replace with your cvc4 binary
    - SymbolicResult: change Z3DIR to z3 directory
