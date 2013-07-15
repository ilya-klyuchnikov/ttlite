organization := "mrsc"

name := "superspec"

scalaVersion := "2.10.2"

libraryDependencies += "mrsc" %% "mrsc" % "0.5"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.5.1"

scalacOptions += "-feature"
