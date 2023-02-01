/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

//
// SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
// Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
// Alexander Fokin, Sergey Levin, Leonid Tsvetkov
//
// This file is part of SmartDec decompiler.
//
// SmartDec decompiler is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// SmartDec decompiler is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
//

#include <nc/config.h>

#include <nc/common/Branding.h>
#include <nc/common/Exception.h>
#include <nc/common/Foreach.h>
#include <nc/common/StreamLogger.h>
#include <nc/common/Unreachable.h>

#include <nc/core/Context.h>
#include <nc/core/Driver.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/ArchitectureRepository.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/arch/Instructions.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Section.h>
#include <nc/core/input/Parser.h>
#include <nc/core/input/ParserRepository.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/cflow/Graphs.h>
#include <nc/core/likec/Tree.h>

#include <QCoreApplication>
#include <QFile>
#include <QStringList>
#include <QTextStream>

#include <nc/core/image/Section.h>

/* CLASSNER CODE START */
#include <QCoreApplication>
#include <QElapsedTimer>
#include <QString>

#include "classner_module/classner.h"
#include "classner_module/rawclass.h"
#include "classner_module/structer.h"
#include "classner_module/classstorer.h"
#include "classner_module/classreader.h"
#include "classner_module/reinterpretalter.h"
#include "classner_module/functionanalyzer.h"

static bool skipClassWrite = false;
static bool skipReinterpret = false;
static bool skipAnalyze = false;
static bool skipRemoveIncluded = false;
static bool skipClassAnalyze = false;
/* CLASSNER CODE END */

const char *self = "nocode";

QTextStream qin(stdin, QIODevice::ReadOnly);
QTextStream qout(stdout, QIODevice::WriteOnly);
QTextStream qerr(stderr, QIODevice::WriteOnly);

template<class T>
void openFileForWritingAndCall(const QString &filename, T functor) {
    if (filename.isEmpty()) {
        return;
    } else if (filename == "-") {
        functor(qout);
    } else {
        QFile file(filename);
        if (!file.open(QIODevice::WriteOnly)) {
            throw nc::Exception("could not open file for writing");
        }
        QTextStream out(&file);
        functor(out);
    }
}

void printSections(nc::core::Context &context, QTextStream &out) {
    foreach (auto section, context.image()->sections()) {
        QString flags;
        if (section->isReadable()) {
            flags += QLatin1String("r");
        }
        if (section->isWritable()) {
            flags += QLatin1String("w");
        }
        if (section->isExecutable()) {
            flags += QLatin1String("x");
        }
        if (section->isCode()) {
            flags += QLatin1String(",code");
        }
        if (section->isData()) {
            flags += QLatin1String(",data");
        }
        if (section->isBss()) {
            flags += QLatin1String(",bss");
        }
        out << QString(QLatin1String("section name = '%1', start = 0x%2, size = 0x%3, flags = %4"))
            .arg(section->name()).arg(section->addr(), 0, 16).arg(section->size(), 0, 16).arg(flags) << '\n';
    }
    auto entrypoint = context.image()->entrypoint();
    if (entrypoint) {
        out << QString(QLatin1String("entry point = 0x%1")).arg(*entrypoint, 0, 16) << '\n';
    }
}

void printSymbols(nc::core::Context &context, QTextStream &out) {
    foreach (const auto *symbol, context.image()->symbols()) {
        QString value;
        if (symbol->value()) {
            value = QString("%1").arg(*symbol->value(), 0, 16);
        } else {
            value = QLatin1String("Undefined");
        }
        out << QString("symbol name = '%1', type = %2, value = 0x%3, section = %4")
            .arg(symbol->name()).arg(symbol->type().getName()).arg(value)
            .arg(symbol->section() ? symbol->section()->name() : QString()) << '\n';
    }
}

void printRegionGraphs(nc::core::Context &context, QTextStream &out) {
    out << "digraph Functions { compound=true; " << '\n';
    foreach (const auto *function, context.functions()->list()) {
        context.graphs()->at(function)->print(out);
    }
    out << "}" << '\n';
}

void help() {
    auto branding = nc::branding();
    branding.setApplicationName("Nocode");

    qout << "Usage: " << self << " [options] [--] file..." << '\n'
         << '\n'
         << "Options:" << '\n'
         << "  --help, -h                  Produce this help message and quit." << '\n'
         << "  --verbose, -v               Print progress information to stderr." << '\n'
         << "  --print-sections[=FILE]     Print information about sections of the executable file." << '\n'
         << "  --print-symbols[=FILE]      Print the symbols from the executable file." << '\n'
         << "  --print-instructions[=FILE] Print parsed instructions to the file." << '\n'
         << "  --print-cfg[=FILE]          Print control flow graph in DOT language to the file." << '\n'
         << "  --print-ir[=FILE]           Print intermediate representation in DOT language to the file." << '\n'
         << "  --print-regions[=FILE]      Print results of structural analysis in DOT language to the file." << '\n'
         << "  --print-cxx[=FILE]          Print reconstructed program into given file." << '\n'
         << "  --from[=ADDR]               From disassemble boundary." << '\n'
         << "  --to[=ADDR]                 To disassemble boundary." << '\n'
         << '\n'
         << branding.applicationName() << " is a command-line native code to C/C++ decompiler." << '\n'
         << "It parses given files, decompiles them, and prints the requested" << '\n'
         << "information (by default, C++ code) to the specified files." << '\n'
         << "When a file name is '-' or omitted, stdout is used." << '\n'
         << '\n';

    qout << "Version: " << branding.applicationVersion() << '\n';

    qout << "Available architectures:";
    foreach (auto architecture, nc::core::arch::ArchitectureRepository::instance()->architectures()) {
        qout << " " << architecture->name();
    }
    qout << '\n';
    qout << "Available parsers:";
    foreach(auto parser, nc::core::input::ParserRepository::instance()->parsers()) {
        qout << " " << parser->name();
    }
    qout << '\n';
    qout << "Report bugs to: " << branding.reportBugsTo() << '\n';
    qout << "License: " << branding.licenseName() << " <" << branding.licenseUrl() << ">" << '\n';
}


/* CLASSNER CODE START */
static bool argumentExists(QString arg, const char* search)
{
  return arg == QString(search);
}

static void printElapsedTime(QElapsedTimer *elapsedTimer)
{
  ulong msecs = elapsedTimer->elapsed();
  ulong secs = msecs / 1000;
  if ((msecs % 1000) > 0) secs++;
  ulong hours = secs / 3600;
  secs = secs % 3600;
  ulong mins = secs / 60;
  secs = secs % 60;
  qout << "Time taken: " << hours << ":" << mins << ":" << secs << Qt::endl;
}

static void printSkipOptions()
{
  // print options
  qout << "SkipClassWrite: " << ((skipClassWrite) ? "True" : "False") << Qt::endl;
  qout << "SkipReinterpret: " << ((skipReinterpret) ? "True" : "False") << Qt::endl;
  qout << "SkipAnalyze: " << ((skipAnalyze) ? "True" : "False") << Qt::endl;
  qout << "SkipRemoveIncluded: " << ((skipRemoveIncluded) ? "True" : "False") << Qt::endl;
  qout << "SkipClassAnalyze: " << ((skipClassAnalyze) ? "True" : "False") << Qt::endl;
}


int optimizeDecompiledCodeStructure(QStringList argv, QString filePath) {
  int argc = argv.size();
  if (argc > 0) {
      for (int i = 0; i < argc; i++) {
          if (argumentExists(argv[i], "-sc"))
              skipClassWrite = true;
          else if (argumentExists(argv[i], "-sr"))
              skipReinterpret = true;
          else if (argumentExists(argv[i], "-sa"))
              skipAnalyze = true;
          else if (argumentExists(argv[i], "-si"))
              skipRemoveIncluded = true;
          else if (argumentExists(argv[i], "-sa2"))
              skipClassAnalyze = true;
          else if (argumentExists(argv[i], "--skip-all")){
              skipClassWrite = true;
              skipReinterpret = true;
              skipAnalyze = true;
              skipRemoveIncluded = true;
              skipClassAnalyze = true;
          }
      }
  }

  printSkipOptions();


  if (filePath.isEmpty()) {
      qout << "No file given!" << Qt::endl;
      return 1;
  }

  // Start program time watch
  QElapsedTimer elapsedTimer;
  elapsedTimer.start();


  qout << "Processing " << filePath.toStdString().c_str() << "..." << Qt::endl;

  ClassStorer::initValues();

  Structer structer;
  structer.readStructs(filePath);

  Classner classner;
  classner.readClassFunctions(filePath, skipClassWrite);
  vector<RawClass> classes = classner.getClasses();

  ClassStorer classStorer(structer, classes);

  if (!skipClassWrite) {
    classStorer.writeClasses();
    classStorer.updateNewCppFile(filePath/*, classes*/);
  }

  if (!skipReinterpret) {
    ReinterpretAlter reinterpret;
    reinterpret.removeReinterpret(classes);
  }

  ClassReader classReader;
  classReader.readClasses();
  map<QString, FixedClass> modifiedClasses = classReader.getClasses();

  // remove default cpp file from class check - change later with different behavior
  QStringList pathArray = filePath.split("/");
  QString fileName = pathArray.back().split(".")[0];
  modifiedClasses.erase(fileName);

  //map<QString, FixedClass> bakModClasses;
  //foreach (auto c, modifiedClasses) {
  //    bakModClasses.insert_or_assign(c.first, c.second);
  //}

  if (!skipAnalyze) {
      FunctionAnalyzer funcAnalyzer;
      map<QString, FixedClass> fixedClasses = funcAnalyzer.findOriginalClass(&modifiedClasses);
      map<QString, QStringList> classIncludes = funcAnalyzer.addUsedClassImports(&fixedClasses, &classes); // FIXME: bottleneck!!!
      // fixed_classes = analyzer.removeInvalidParams(fixed_classes, classes) # FIXME: broken at the moment
      classStorer.writeClassesJust(fixedClasses, classIncludes);
  }

  if (!skipRemoveIncluded) {
      qout << "Remove included [not implemented yet]" << Qt::endl;
      // TODO: Python equivalen: os.system("cd generated_classes && python3 remove_included.py")
  }

  if (!skipClassAnalyze) {
      qout << "Class Analyze [not implemented yet]" << Qt::endl;
      // TODO: Python equivalent
      // classAnalyzer = ClassAnalyzer()
      // classAnalyzer.findClassAttributes(bak_mod_classes) # FIXME: only works when previous are done and skipped second run
      // - - -
      //gotogo = Gotogo()
      //gotogo.processClasses(modified_classes)
      //os.system("mv *_*.cpp Qt::endl/class_info/") # FIXME: change later
  }


  // Stop program time watch
  printElapsedTime(&elapsedTimer);
  elapsedTimer.invalidate();

  return 0;
}
/* CLASSNER CODE END */


int main(int argc, char *argv[]) {
    QCoreApplication app(argc, argv);

    try {
        QString sectionsFile;
        QString symbolsFile;
        QString instructionsFile;
        QString cfgFile;
        QString irFile;
        QString regionsFile;
        QString cxxFile;
        nc::ByteAddr from_addr = 0;
        nc::ByteAddr to_addr = 0;

        bool autoDefault = true;
        bool verbose = false;

        std::vector<nc::ByteAddr> functionAddresses;
        std::vector<nc::ByteAddr> callAddresses;

        QStringList files;

        auto args = QCoreApplication::arguments();

        for (int i = 1; i < args.size(); ++i) {
            QString arg = args[i];
            if (arg == "--help" || arg == "-h") {
                help();
                return 1;
            } else if (arg == "--verbose" || arg == "-v") {
                verbose = true;

            #define FILE_OPTION(option, variable)       \
            } else if (arg == option) {                 \
                variable = "-";                         \
                autoDefault = false;                    \
            } else if (arg.startsWith(option "=")) {    \
                variable = arg.section('=', 1);         \
                autoDefault = false;
            #define ADDR_OPTION(option, variable)                   \
            } else if (arg.startsWith(option "=")) {                \
                bool ok;                                            \
                variable = arg.section('=', 1).toInt(&ok,16);       \
                autoDefault = true;

            FILE_OPTION("--print-sections", sectionsFile)
            FILE_OPTION("--print-symbols", symbolsFile)
            FILE_OPTION("--print-instructions", instructionsFile)
            FILE_OPTION("--print-cfg", cfgFile)
            FILE_OPTION("--print-ir", irFile)
            FILE_OPTION("--print-regions", regionsFile)
            FILE_OPTION("--print-cxx", cxxFile)
            ADDR_OPTION("--from", from_addr)
            ADDR_OPTION("--to", to_addr)

            #undef FILE_OPTION
            #undef ADDR_OPTION

            } else if (arg == "--") {
                while (++i < args.size()) {
                    files.append(args[i]);
                }
            } else if (arg.startsWith("-")) {
                throw nc::Exception(QString("unknown argument: %1").arg(arg));
            } else {
                files.append(args[i]);
            }
        }

        if (autoDefault) {
            cxxFile = "-";
        }

        if (files.empty()) {
            throw nc::Exception("no input files");
        }

        nc::core::Context context;

        if (verbose) {
            context.setLogToken(nc::LogToken(std::make_shared<nc::StreamLogger>(qerr)));
        }

        foreach (const QString &filename, files) {
            try {
                nc::core::Driver::parse(context, filename);
            } catch (const nc::Exception &e) {
                throw nc::Exception(filename + ":" + e.unicodeWhat());
            } catch (const std::exception &e) {
                throw nc::Exception(filename + ":" + e.what());
            }
        }

        openFileForWritingAndCall(sectionsFile, [&](QTextStream &out) { printSections(context, out); });
        openFileForWritingAndCall(symbolsFile, [&](QTextStream &out) { printSymbols(context, out); });

        if (!instructionsFile.isEmpty() || !cfgFile.isEmpty() || !irFile.isEmpty() || !regionsFile.isEmpty() || !cxxFile.isEmpty()) {
            if(from_addr && to_addr)
            {
                foreach (const nc::core::image::Section *section, context.image()->sections())
                    if( from_addr >= section->addr() && to_addr <= section->endAddr() )
                        nc::core::Driver::disassemble(context, section, from_addr, to_addr);
            }
            else
                nc::core::Driver::disassemble(context);

            openFileForWritingAndCall(instructionsFile, [&](QTextStream &out) { context.instructions()->print(out); });

            if (!cfgFile.isEmpty() || !irFile.isEmpty() || !regionsFile.isEmpty() || !cxxFile.isEmpty()) {
                nc::core::Driver::decompile(context);

                openFileForWritingAndCall(cfgFile,     [&](QTextStream &out) { context.program()->print(out); });
                openFileForWritingAndCall(irFile,      [&](QTextStream &out) { context.functions()->print(out); });
                openFileForWritingAndCall(regionsFile, [&](QTextStream &out) { printRegionGraphs(context, out); });
                openFileForWritingAndCall(cxxFile,     [&](QTextStream &out) { context.tree()->print(out); });
            }
        }

        // classner code
        int result = optimizeDecompiledCodeStructure(args, cxxFile);
        if (result != 0) return result; // return error code from classner instead
    } catch (const nc::Exception &e) {
        qerr << self << ": " << e.unicodeWhat() << '\n';
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
