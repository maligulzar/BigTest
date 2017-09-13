name := "ScalaSymbolicExecution"

version := "1.0"

scalaVersion := "2.10.6"

mainClass in assembly := Some("SymexScala.Main")

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-reflect" % scalaVersion.value,
    //"com.github.scala-incubator.io" %% "scala-io-file" % "0.4.2",
    "org.scalatest" %% "scalatest" % "3.0.1" % "test"
    )

libraryDependencies ++= Seq(
    ("org.apache.spark" %% "spark-core" % "1.6.2" % "provided").
    exclude("org.mortbay.jetty", "servlet-api").
    exclude("commons-beanutils", "commons-beanutils-core").
    exclude("commons-collections", "commons-collections").
    exclude("commons-logging", "commons-logging").
    exclude("com.esotericsoftware.minlog", "minlog")
)

assemblyMergeStrategy in assembly := {
    case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
    case x => 
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
}