#include <cstdlib>
#include <lld/Common/Driver.h>
#include <mutex>
#include <iostream>

using namespace llvm;

const char *alloc_str(const std::string &str) {
    size_t size = str.length();
    if (size > 0) {
        char *strPtr = reinterpret_cast<char *>(malloc(size + 1));
        memcpy(strPtr, str.c_str(), size + 1);
        return strPtr;
    }
    return nullptr;
}

// LLD seems not to be thread safe
std::mutex _wasmMutex;

extern "C" {
    struct LLDInvokeResult {
        bool success;
        const char *messages;
    };

    void link_free_result(LLDInvokeResult *result) {
        if (result->messages) {
            free(reinterpret_cast<void *>(const_cast<char *>(result->messages)));
        }
    }

    LLDInvokeResult lld_link(const char *flavor, int argc, const char *const *argv) {
        std::string outputString, errorString;
        llvm::raw_string_ostream outputStream(outputString);
        llvm::raw_string_ostream errorStream(errorString);
        std::vector<const char *> args(argv, argv + argc);
        LLDInvokeResult result;
        std::unique_lock<std::mutex> lock(_wasmMutex);

        std::string flavorStr(flavor);
        if (flavorStr.compare("coff") == 0 ||
            flavorStr.compare("windows") == 0) {
            result.success = lld::coff::link(args, false, outputStream, errorStream);
        }
        else if (flavorStr.compare("mingw") == 0) {
            result.success = lld::mingw::link(args, false, outputStream, errorStream);
        }
        else if (flavorStr.compare("elf") == 0 ||
                 flavorStr.compare("linux") == 0 ||
                 flavorStr.compare("unix") == 0) {
            result.success = lld::elf::link(args, false, outputStream, errorStream);
        }
        else if (flavorStr.compare("mach-o") == 0 ||
                 flavorStr.compare("darwin") == 0 ||
                 flavorStr.compare("ios") == 0 ||
                 flavorStr.compare("tvos") == 0 ||
                 flavorStr.compare("macos") == 0 ||
                 flavorStr.compare("macosx") == 0) {
          result.success =
              lld::mach_o::link(args, false, outputStream, errorStream);
        }
        // else if (flavorStr.compare("macho") == 0 ||
        //          flavorStr.compare("darwinnew") == 0) {
        //   result.success =
        //       lld::macho::link(args, false, outputStream, errorStream);
        
        // }
        else if (flavorStr.compare("wasm") == 0 ||
                   flavorStr.compare("wasi") == 0 ||
                   flavorStr.compare("wasm32") == 0 ||
                   flavorStr.compare("wasm32-wasi") == 0 ||
                   flavorStr.compare("wasm32-unknown-wasi") == 0) {
          result.success =
              lld::wasm::link(args, false, outputStream, errorStream);
        } else {
          result.success = false;
          errorStream << "Unknown flavor: " << flavor << "\n";
        }

        std::string resultMessage = errorStream.str() + outputStream.str();
        result.messages = alloc_str(resultMessage);
        return result;
    }
}
