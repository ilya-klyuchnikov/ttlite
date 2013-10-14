import sbt._
import Keys._

object TTLiteBuild extends Build {

  override lazy val settings = super.settings ++ Seq(scalaVersion := "2.10.3")

  lazy val CoreProject = Project("ttlite-core", file("ttlite-core"),
    settings = Project.defaultSettings ++ Seq(
      organization := "ttlite",
      name := "core",
      version := "0.1",
      libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.5.1",
      libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test",
      baseDirectory in run := file("."),
      testOptions in Test += Tests.Argument("-oD")
    )
  )

  lazy val ScProject = Project("ttlite-sc", file("ttlite-sc"),
    settings = Project.defaultSettings ++ Seq(
      organization := "ttlite",
      name := "sc",
      version := "0.1",
      libraryDependencies += "mrsc" %% "mrsc" % "0.5",
      libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test",
      baseDirectory in run := file("."),
      testOptions in Test += Tests.Argument("-oD"),
      resolvers += "lambdamix-bintray" at "http://dl.bintray.com/lambdamix/maven/",
      // vargen is not thread-safe
      parallelExecution in Test := false
    )
  ) dependsOn CoreProject

  lazy val root = Project(id = "ttlite", base = file(".")) aggregate(CoreProject, ScProject)
}
