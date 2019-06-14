# Test-Minimization-in-Big-Data

## Download latest version of Scala-IDE (this was tested on eclipse 4.7.1)
    Copy only my code changes into a functional end-to-end application
    Will need to set up eclipse configs from Gulzar
        Import each project into eclipse using Java/Scala project (use source as working directory)
        copy archive contents (that gulzar sent) into jpf-integrated folder
        
  ### Download z3 repo in base project dir
        https://github.com/Z3Prover/z3
        https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang
        Also set up python bindings
            https://github.com/Z3Prover/z3#python
  ### Install cvc4 (I lucked out andhad it already)
        SymbolicResult: line 74ish, replace with your cvc4 binary
    SymbolicResult: change Z3DIR to z3 directory
  
        
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
            alt: comment out the two scala files
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
  
  
  # Run: 
        Configurations -> Java Applications -> run-JPF-symbc (change VM argument for java lib path)
        Uncomment Test2.scala (from SymExec)
        may need to re-export symex + udfextractor (uncomment the examples dir if so)
            do this for both jpf-core and jpf-symbc
        Update JPF.java (jpf-core)
        ignore warnings when launching
### TODO along the way: find and replace "up_jpf" -> "Test-..."
    also check for malig on path
        Gulzar: Configuration and SystemCommandHandler
    also check for amytis (Shagha)
